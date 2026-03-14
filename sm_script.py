"""
Facebook Post Sharer Tracker
-----------------------------
Opens the real facebook.com post in a browser, clicks the "X shares" button,
scrolls through the shares dialog, and counts how many times each name appears.

Requirements:
    pip install selenium webdriver-manager beautifulsoup4

Usage:
    1. Paste the Facebook post URL into POST_URL below.
    2. Run:  python sm_script.py

DISCLAIMER:
    - This tool is intended for research and awareness of disinformation campaigns.
    - Use it responsibly and in accordance with Facebook's Terms of Service.
    - Works on truly public posts. Private or restricted posts will show a login wall.
"""

# ===========================================================================
#  PASTE YOUR FACEBOOK POST LINK HERE
# ===========================================================================
POST_URL = ""
# Example:
# POST_URL = "https://www.facebook.com/SomePage/posts/1234567890"
# ===========================================================================

import re
import os
import sys
import time
import json
import base64
import ctypes
import ctypes.wintypes
import shutil
import tempfile
from collections import Counter
from cryptography.hazmat.primitives.ciphers.aead import AESGCM

from bs4 import BeautifulSoup
from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.common.action_chains import ActionChains
from selenium.webdriver.common.keys import Keys
from selenium.common.exceptions import TimeoutException, StaleElementReferenceException
from webdriver_manager.chrome import ChromeDriverManager


# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

# Seconds to wait after consent / page navigation
PAGE_LOAD_PAUSE = 3.0

# Pixels to scroll inside the shares dialog per step
SCROLL_STEP_PX = 500

# Seconds between scroll steps
SCROLL_PAUSE = 1.2

# Stop scrolling after this many consecutive steps with no new names found
MAX_EMPTY_SCROLLS = 10

# Set to True to save dialog HTML snapshots per scroll pass and print per-name debug info
DEBUG = True

# Holds the raw Selenium WebElement for the aria-label shares container.
# Populated at runtime so you can inspect it at the breakpoint().
_DEBUG_SHARES_ARIA_EL = None

# Words that appear as link text but are NOT sharer names
SKIP_WORDS = {
    "", "like", "comment", "share", "shares", "follow", "more", "see more",
    "see all", "view", "reply", "next", "previous", "back", "home",
    "facebook", "log in", "sign up", "menu", "settings", "privacy",
    "terms", "help", "cookies", "write a comment", "send",
}


# ---------------------------------------------------------------------------
# Browser setup
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Chrome cookie extraction (decrypt from running Chrome — no profile copy)
# ---------------------------------------------------------------------------

class _DataBlob(ctypes.Structure):
    _fields_ = [("cbData", ctypes.wintypes.DWORD),
                ("pbData", ctypes.POINTER(ctypes.c_char))]


def _dpapi_decrypt(ciphertext: bytes) -> bytes:
    """Decrypt bytes with Windows DPAPI (CryptUnprotectData)."""
    buf = ctypes.create_string_buffer(ciphertext, len(ciphertext))
    blob_in = _DataBlob(ctypes.sizeof(buf), buf)
    blob_out = _DataBlob()
    ok = ctypes.windll.crypt32.CryptUnprotectData(
        ctypes.byref(blob_in), None, None, None, None, 0, ctypes.byref(blob_out)
    )
    if not ok:
        raise RuntimeError("DPAPI decryption failed")
    result = ctypes.string_at(blob_out.pbData, blob_out.cbData)
    ctypes.windll.kernel32.LocalFree(blob_out.pbData)
    return result


def _get_chrome_aes_key() -> bytes | None:
    """Read and decrypt the AES-256 key Chrome uses to encrypt cookies."""
    local_state_path = os.path.join(
        os.environ.get("LOCALAPPDATA", ""), "Google", "Chrome", "User Data", "Local State"
    )
    try:
        with open(local_state_path, "r", encoding="utf-8") as f:
            ls = json.load(f)
        enc_key_b64 = ls["os_crypt"]["encrypted_key"]
        enc_key = base64.b64decode(enc_key_b64)[5:]  # strip 'DPAPI' prefix
        return _dpapi_decrypt(enc_key)
    except Exception as e:
        print(f"[!] Could not read Chrome AES key: {e}")
        return None


def _decrypt_cookie_value(enc_value: bytes, aes_key: bytes) -> str:
    """Decrypt a single Chrome cookie value (v10/v11 = AES-GCM, else DPAPI)."""
    if not enc_value:
        return ""
    if enc_value[:3] in (b"v10", b"v11"):
        nonce = enc_value[3:15]
        data = enc_value[15:]
        try:
            return AESGCM(aes_key).decrypt(nonce, data, None).decode("utf-8", errors="replace")
        except Exception:
            return ""
    else:
        try:
            return _dpapi_decrypt(enc_value).decode("utf-8", errors="replace")
        except Exception:
            return ""


def _get_facebook_cookies() -> list[dict]:
    """
    Read and decrypt all Facebook cookies from the user's default Chrome profile.
    Returns a list of cookie dicts ready for driver.add_cookie().
    Works while Chrome is running (copies the DB to a temp file first).
    """
    aes_key = _get_chrome_aes_key()
    if aes_key is None:
        return []

    local_app = os.environ.get("LOCALAPPDATA", "")
    candidates = [
        os.path.join(local_app, "Google", "Chrome", "User Data", "Default", "Network", "Cookies"),
        os.path.join(local_app, "Google", "Chrome", "User Data", "Default", "Cookies"),
    ]
    cookies_db = next((p for p in candidates if os.path.exists(p)), None)
    if cookies_db is None:
        print("[!] Chrome cookies database not found.")
        return []

    import sqlite3
    WIN_EPOCH_DELTA = 11_644_473_600  # seconds between 1601-01-01 and 1970-01-01
    cookies: list[dict] = []

    # Try to copy first (cleaner); fall back to direct read-only URI (works while Chrome runs)
    # NOTE: SQLite URI paths on Windows MUST use forward slashes AND the file:///C:/... form.
    # Using file:C:\path\... (backslashes) or file:C:/path (no triple-slash) both fail.

    def _to_sqlite_uri(path: str, extra: str = "") -> str:
        """Convert an absolute Windows or POSIX path to a valid SQLite file URI."""
        fwd = path.replace("\\", "/")
        if len(fwd) > 1 and fwd[1] == ":":   # Windows drive letter, e.g. C:/...
            return f"file:///{fwd}{extra}"
        return f"file:{fwd}{extra}"

    tmp_db: str | None = None
    try:
        tmp_db = tempfile.mktemp(suffix="_fb_cookies.db")
        shutil.copy2(cookies_db, tmp_db)
        db_uri = _to_sqlite_uri(tmp_db, "?mode=ro")
    except Exception:
        tmp_db = None
        # Open the live DB in immutable/read-only mode — bypasses SQLite WAL lock
        db_uri = _to_sqlite_uri(cookies_db, "?mode=ro&immutable=1")

    try:
        con = sqlite3.connect(db_uri, uri=True)
        con.row_factory = sqlite3.Row
        cur = con.execute(
            "SELECT host_key, name, encrypted_value, path, "
            "       expires_utc, is_secure, is_httponly, samesite "
            "FROM cookies "
            "WHERE host_key LIKE '%facebook.com%' "
            "   OR host_key LIKE '%fbcdn.net%'"
        )
        for row in cur.fetchall():
            value = _decrypt_cookie_value(bytes(row["encrypted_value"]), aes_key)
            if not value:
                continue
            cookie: dict = {
                "name": row["name"],
                "value": value,
                "domain": row["host_key"],
                "path": row["path"],
                "secure": bool(row["is_secure"]),
                "httpOnly": bool(row["is_httponly"]),
            }
            exp = row["expires_utc"]
            if exp:
                unix_exp = exp // 1_000_000 - WIN_EPOCH_DELTA
                if unix_exp > 0:
                    cookie["expiry"] = unix_exp
            cookies.append(cookie)
        con.close()
    except Exception as e:
        print(f"[!] Error reading cookies: {e}")
    finally:
        if tmp_db:
            try:
                os.unlink(tmp_db)
            except Exception:
                pass
    return cookies


def build_driver() -> webdriver.Chrome:
    """Create a headless Chrome WebDriver and inject Facebook session cookies.

    Reads cookies directly from the running Chrome profile (no profile copy,
    no profile lock conflicts), decrypts them with Windows DPAPI + AES-GCM,
    and injects them into the headless session via driver.add_cookie().
    """
    opts = Options()
    opts.add_argument("--headless=new")          # invisible — no browser window
    opts.add_argument("--window-size=1920,1080")
    opts.add_argument("--disable-notifications")
    opts.add_argument("--disable-popup-blocking")
    opts.add_argument("--lang=en-US")
    opts.add_argument("--no-sandbox")
    opts.add_argument("--disable-dev-shm-usage")
    opts.add_argument("--disable-gpu")
    opts.add_argument(
        "user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/122.0.0.0 Safari/537.36"
    )
    opts.add_experimental_option("excludeSwitches", ["enable-automation"])
    opts.add_experimental_option("useAutomationExtension", False)

    service = Service(ChromeDriverManager().install())
    driver = webdriver.Chrome(service=service, options=opts)
    driver.execute_cdp_cmd(
        "Page.addScriptToEvaluateOnNewDocument",
        {"source": "Object.defineProperty(navigator,'webdriver',{get:()=>undefined})"},
    )

    # Navigate to FB first (cookies must be set on the right domain)
    driver.get("https://www.facebook.com")
    time.sleep(1.0)

    fb_cookies = _get_facebook_cookies()
    if fb_cookies:
        for cookie in fb_cookies:
            try:
                driver.add_cookie(cookie)
            except Exception:
                pass
        print(f"[+] Injected {len(fb_cookies)} Facebook cookies from Chrome profile.")
    else:
        print("[!] No Facebook cookies found; running in anonymous mode.")

    return driver


def accept_consent(driver: webdriver.Chrome, timeout: int = 8) -> bool:
    """
    Dismiss the cookie/GDPR consent overlay.
    Tries normal click first, then JavaScript click as fallback.
    Returns True if a consent button was found and clicked.
    Pass a smaller timeout (e.g. 3) for a quick second-pass check.
    """
    xpaths = [
        "//button[contains(.,'Allow all cookies')]",
        "//button[contains(.,'Accept all')]",
        "//button[contains(.,'Allow all')]",
        "//button[contains(.,'Accept')]",
        "//button[contains(.,'Allow')]",
        "//button[contains(.,'Reject non-essential')]",  # dismisses without accepting
        "//div[@aria-label='Allow all cookies']",
        "//div[@data-cookiebanner='accept_button']",
    ]
    for xpath in xpaths:
        try:
            btn = WebDriverWait(driver, timeout).until(
                EC.presence_of_element_located((By.XPATH, xpath))
            )
            # Scroll into view and try normal click, fall back to JS click
            driver.execute_script("arguments[0].scrollIntoView(true);", btn)
            try:
                btn.click()
            except Exception:
                driver.execute_script("arguments[0].click();", btn)
            print("[+] Cookie consent accepted.")
            time.sleep(2.0)
            return True
        except TimeoutException:
            continue
    return False  # no consent banner (fine in some regions)


def wait_for_post_body(driver: webdriver.Chrome, timeout: int = 15) -> bool:
    """
    Wait until the actual post content is present in the DOM.
    Returns True when ready, False on timeout.
    """
    post_selectors = [
        "[role='article']",
        "[data-pagelet='FeedUnit_0']",
        ".x1yztbdb",          # common FB post wrapper class (may change)
        "[data-ad-preview='message']",
    ]
    for sel in post_selectors:
        try:
            WebDriverWait(driver, timeout).until(
                EC.presence_of_element_located((By.CSS_SELECTOR, sel))
            )
            return True
        except TimeoutException:
            continue
    return False


def click_shares_button(driver: webdriver.Chrome) -> bool:
    """
    Find and click the 'N shares' COUNT button on the post page.
    Pass 1 checks aria-label (most precise — avoids the compose-share button).
    Pass 2 falls back to visible text content.
    Returns True if successfully clicked, False otherwise.
    """

    def _try_click(el) -> bool:
        try:
            driver.execute_script("arguments[0].scrollIntoView({block:'center'});", el)
            time.sleep(0.3)
            try:
                el.click()
            except Exception:
                driver.execute_script("arguments[0].click();", el)
            return True
        except Exception:
            return False

    # Pass 1: aria-label containing 'share' + a digit.
    # The shares COUNT button has aria-label like "24 shares" or "See 24 shares".
    # The compose-SHARE action button says just "Share" with no digit — filtered out.
    for el in driver.find_elements(
        By.XPATH,
        "//*[contains(translate(@aria-label,'ABCDEFGHIJKLMNOPQRSTUVWXYZ',"
        "'abcdefghijklmnopqrstuvwxyz'),'share')]"
    ):
        try:
            lbl = (el.get_attribute('aria-label') or '').strip()
            if re.search(r'\d', lbl) and re.search(r'share', lbl, re.I):
                if _try_click(el):
                    print(f"[+] Clicked shares button (aria-label='{lbl}')")
                    time.sleep(6.0)
                    return True
        except StaleElementReferenceException:
            continue

    # Pass 2: visible text node containing 'share' + a digit.
    for el in driver.find_elements(
        By.XPATH,
        "//*[contains(translate(text(),'ABCDEFGHIJKLMNOPQRSTUVWXYZ',"
        "'abcdefghijklmnopqrstuvwxyz'),'share')]"
    ):
        try:
            text = el.text.strip()
            if not text:
                continue
            if re.search(r'\d', text) and re.search(r'share', text, re.I):
                if _try_click(el):
                    print(f"[+] Clicked shares button (text='{text}')")
                    time.sleep(6.0)
                    return True
        except StaleElementReferenceException:
            continue

    return False


def find_shares_dialog(driver: webdriver.Chrome):
    """
    Return the shares dialog element after the shares button was clicked.
    We specifically look for a dialog whose heading mentions 'share'.
    Returns None if not found.
    """
    # First try: dialog with a share-related aria-label or heading
    specific = [
        "//div[@role='dialog'][.//*[contains(translate(text(),"
        "'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'),'share')]]",
    ]
    for xpath in specific:
        try:
            els = driver.find_elements(By.XPATH, xpath)
            if els:
                return els[-1]
        except Exception:
            continue

    # Fallback: the most recently opened dialog (last in DOM)
    try:
        dialogs = driver.find_elements(By.XPATH, "//div[@role='dialog']")
        if dialogs:
            return dialogs[-1]
    except Exception:
        pass

    return None


def collect_names_from_dialog(driver: webdriver.Chrome, dialog, debug: bool = False) -> list[str]:
    """
    Scroll through the shares dialog and return ALL sharer names (with duplicates).

    Duplicates are intentional: the same person can share multiple times and
    each share is a separate [role="article"] card. build_share_counter() will
    count how many times each name appears.

    The dialog WebElement is NEVER used for DOM queries after being passed in —
    it can go stale silently.  Everything is queried fresh from the document
    root on every iteration using driver.find_elements or execute_script.
    """

    SKIP_ARIA = {
        "close", "actions for this post", "show attachment",
        "loading...", "menu", "more", "back",
        "see who reacted to this", "shared with public", "shared with friends",
        "shared with friends of friends", "shared with only me",
    }

    TIMESTAMP_RE = re.compile(
        r'^(\d+\s*(m|h|d|w|s|мин|ч|д|лв|сек|min|sec|hr|hrs|just\s*now|now))$',
        re.I | re.U,
    )

    def _is_valid(name: str) -> bool:
        if not name or len(name) < 2:
            return False
        if TIMESTAMP_RE.match(name):
            return False
        if name.lower() in SKIP_WORDS or name.lower() in SKIP_ARIA:
            return False
        if name.isdigit() or re.match(r'^[\d\s,·.]+$', name):
            return False
        return True

    global _DEBUG_SHARES_ARIA_EL
    _DEBUG_SHARES_ARIA_EL = dialog

    SKIP_LIST = list(SKIP_ARIA | {w.lower() for w in SKIP_WORDS})

    # ── Scope all DOM queries to THIS specific dialog, not just any dialog ─
    # Problem: Facebook wraps posts/feeds in [role="dialog"] elements for
    # accessibility, so '[role="dialog"] [role="article"]' would match comment
    # articles in the main post dialog, not sharer cards in the shares dialog.
    # Fix: mark the shares dialog with a unique data attribute and use that
    # attribute as the CSS scope for every article search.
    _DLG_ATTR = 'data-fb-shares-tracker'
    _DLG_SEL  = f'[{_DLG_ATTR}="1"] [role="article"]'
    try:
        driver.execute_script(
            f"arguments[0].setAttribute('{_DLG_ATTR}','1');", dialog)
    except Exception:
        # If the element is already stale, fall back to generic (less precise)
        _DLG_SEL = '[role="dialog"] [role="article"]'

    # ── JS: extract name from ONE article element ─────────────────────────
    # arguments[0] = the article WebElement
    # arguments[1] = SKIP_LIST
    #
    # KEY FIX — dirty name "Велислава ХристоваPosted to PAGE":
    #   The profile_name div contains:
    #     <a href="/profile">Велислава Христова</a> posted to <a href="/page">PAGE</a>
    #   Strategy order: a[role="link"] → profile_name div → a[aria-label].
    #   Returns {name, href, tid} so the caller can deduplicate by share event,
    #   not by person (same person sharing twice → two distinct tid values).
    JS_NAME_FROM_ARTICLE = r"""
        var art  = arguments[0];
        var skip = arguments[1];

        function ok(t) {
            t = (t || '').trim();
            return t.length > 1 && skip.indexOf(t.toLowerCase()) < 0 ? t : null;
        }

        var name = null, href = '', tid = '';

        // Strategy 1: a[role="link"] – most reliable selector in shares dialog.
        // Facebook always renders the sharer's profile name as a role=link anchor.
        var roleLinks = art.querySelectorAll('a[role="link"]');
        for (var i = 0; i < roleLinks.length; i++) {
            var t = ok(roleLinks[i].textContent);
            if (t) { name = t; href = roleLinks[i].href || ''; break; }
        }

        // Strategy 2: profile_name div (older / alternative layout)
        if (!name) {
            var pn = art.querySelector('[data-ad-rendering-role="profile_name"]');
            if (pn) {
                var a = pn.querySelector('a');
                if (a) { var t = ok(a.textContent); if (t) { name = t; href = a.href || ''; } }
                if (!name) {
                    var b = pn.querySelector('b');
                    if (b) { var s = b.querySelector('span'); var t = ok((s||b).textContent); if (t) name = t; }
                }
            }
        }

        // Strategy 3: avatar/profile link aria-label
        if (!name) {
            var aLinks = art.querySelectorAll('a[aria-label]');
            for (var i = 0; i < aLinks.length; i++) {
                var t = ok(aLinks[i].getAttribute('aria-label'));
                if (t) { name = t; href = aLinks[i].href || ''; break; }
            }
        }

        if (!name) return null;

        // Strategy 4: first <a> whose href looks like a Facebook profile URL.
        // Covers /username, /profile.php?id=..., /people/... patterns.
        if (!name) {
            var allAs = art.querySelectorAll('a[href]');
            for (var i = 0; i < allAs.length; i++) {
                var h = allAs[i].href || '';
                if (/facebook\.com\/(profile\.php|people\/|[^\/\?#]{3,}\/?$)/.test(h)) {
                    var t = ok(allAs[i].textContent);
                    if (t) { name = t; href = h; break; }
                }
            }
        }

        // Strategy 5: brute-force — first leaf <span> whose text passes ok().
        // Catches any layout where the name sits in a bare span with no role attr.
        if (!name) {
            var spans = art.querySelectorAll('span');
            for (var i = 0; i < spans.length; i++) {
                // leaf spans only: no child spans (avoids concatenated text)
                if (spans[i].querySelector('span')) continue;
                var t = ok(spans[i].textContent);
                if (t) { name = t; break; }
            }
        }

        if (!name) return null;
        // This lets us count the same person sharing twice as two distinct events.
        var shareLinks = art.querySelectorAll('a[href*="/posts/"], a[href*="/permalink/"]');
        for (var i = 0; i < shareLinks.length; i++) {
            var h = (shareLinks[i].getAttribute('href') || '').trim();
            if (h.length > 15) { tid = h; break; }
        }
        if (!tid) { var te = art.querySelector('[data-utime]'); if (te) tid = te.getAttribute('data-utime') || ''; }
        if (!tid) { var te = art.querySelector('abbr, time'); if (te) tid = (te.textContent || '').trim(); }

        return {name: name, href: href, tid: tid};
    """

    # ── JS: scroll the dialog so the next batch of articles loads ─────────
    # arguments[0] = step in pixels (SCROLL_STEP_PX).
    # Key fix: use scrollHeight > clientHeight to detect the scrollable container.
    # CSS overflowY can be 'hidden' or 'clip' even when the element IS scrollable
    # (FB uses this pattern), so the previous CSS-property check missed it.
    JS_SCROLL = """
        var step = arguments[0];
        var dlg = document.querySelector('[data-fb-shares-tracker="1"]');
        if (!dlg) {
            var _dlgs = document.querySelectorAll('[role="dialog"]');
            dlg = _dlgs.length ? _dlgs[_dlgs.length - 1] : null;
        }
        if (!dlg) return false;

        // Any element whose scrollHeight > clientHeight has scrollable content,
        // regardless of its CSS overflow value.
        var targets = [dlg].concat(Array.prototype.slice.call(dlg.querySelectorAll('*')));
        var scrolled = false;
        for (var i = 0; i < targets.length; i++) {
            var el = targets[i];
            if (el.scrollHeight > el.clientHeight + 2) {
                var before = el.scrollTop;
                el.scrollTop += step;
                if (el.scrollTop !== before) scrolled = true;
                el.dispatchEvent(new WheelEvent('wheel', {
                    deltaY: step, deltaMode: 0, bubbles: true, cancelable: true
                }));
            }
        }

        // scrollIntoView on the very last article's last child
        // → fires Facebook's IntersectionObserver (virtual-list loader)
        var arts = dlg.querySelectorAll('[role="article"]');
        if (arts.length > 0) {
            var last = arts[arts.length - 1];
            var lastChild = last.lastElementChild || last;
            lastChild.scrollIntoView({behavior: 'instant', block: 'end'});
        }
        return scrolled;
    """

    all_names: list[str] = []  # duplicates kept — same person sharing N times = N entries
    seen_shares: set[tuple] = set()
    empty_rounds = 0
    consecutive_loading_stall = 0   # passes where ONLY skeleton articles appear
    MAX_LOADING_STALL = 6           # give up if skeletons never resolve
    iteration = 0

    # Wait up to 15 s for the first sharer cards to appear
    print("[*] Waiting for sharer cards to render...")
    for _w in range(15):
        _initial = driver.find_elements(By.CSS_SELECTOR, _DLG_SEL)
        if _initial:
            break
        time.sleep(1.0)
    else:
        print("[!] No sharer articles appeared in 15 s – dialog may not be open.")
        return []
    print(f"[*] Found first batch ({len(_initial)} card(s)). Collecting all names...")

    while empty_rounds < MAX_EMPTY_SCROLLS:

        # ── fetch articles from the MARKED shares dialog only ───────────
        try:
            articles = driver.find_elements(By.CSS_SELECTOR, _DLG_SEL)
        except Exception:
            break

        new_this_round = 0
        loading_this_round = 0
        for article in articles:
            # ── Skip skeleton/loading placeholder articles ─────────────────
            # FB renders shimmer-placeholder articles (aria-label="Loading...")
            # while waiting for real data; these have no name to extract.
            try:
                if article.find_elements(By.CSS_SELECTOR, '[aria-label="Loading..."]'):
                    loading_this_round += 1
                    continue
            except StaleElementReferenceException:
                continue
            except Exception:
                pass

            # ── Scroll this article into view one by one ──────────────────
            # Brings each card into the viewport before extracting its name.
            # This triggers IntersectionObserver incrementally so FB's virtual
            # list loads names/avatars progressively instead of skipping items.
            try:
                driver.execute_script(
                    "arguments[0].scrollIntoView({behavior:'instant',block:'nearest'});",
                    article,
                )
                time.sleep(0.15)   # let lazy content (aria-labels, spans) render
            except StaleElementReferenceException:
                continue
            except Exception:
                pass   # non-fatal — try name extraction anyway

            try:
                result = driver.execute_script(JS_NAME_FROM_ARTICLE, article, SKIP_LIST)
            except (StaleElementReferenceException, Exception):
                continue

            if not result:
                continue

            # JS now returns a dict; tolerate plain string fallback just in case
            if isinstance(result, dict):
                name = result.get('name') or ''
                href = result.get('href') or ''
                tid  = result.get('tid')  or ''
            else:
                name, href, tid = str(result), '', ''

            if not name or not _is_valid(name):
                continue

            # Build a unique key per share-event (not per person).
            # If we have a permalink (tid) or at least a profile URL (href), use them;
            # otherwise fall back to name-only (slight risk of missing a share, but
            # name-only dedup is the safer choice over counting ghost duplicates).
            key: tuple = (name, href, tid) if (href or tid) else (name,)
            if key in seen_shares:
                continue   # already recorded this exact share

            seen_shares.add(key)
            all_names.append(name)
            new_this_round += 1
            print(f"  [+] ({len(all_names)}) {name}")

        # Diagnostic: on the very first pass with 0 results, dump article HTML
        if loading_this_round:
            print(f"  [pass {iteration}] {loading_this_round} skeleton article(s) still loading — skipped")
        if iteration == 0 and new_this_round == 0 and articles:
            try:
                art_html = driver.execute_script(
                    "return arguments[0].outerHTML;", articles[0])
                with open("debug_article_0.html", "w", encoding="utf-8") as fh:
                    fh.write(art_html or "(empty)")
                print("  [DIAG] 0 names on first pass — saved first article HTML "
                      "\u2192 debug_article_0.html  (open it to inspect the DOM)")
            except Exception as _de:
                print(f"  [DIAG] Could not dump article HTML: {_de}")

        real_articles = len(articles) - loading_this_round
        print(f"  [pass {iteration}] DOM articles: {len(articles)} "
              f"({real_articles} real, {loading_this_round} loading), "
              f"new unique shares: {new_this_round}, "
              f"total so far: {len(all_names)}, "
              f"empty rounds: {empty_rounds}/{MAX_EMPTY_SCROLLS}")

        if debug:
            try:
                html = driver.execute_script(
                    "var d=document.querySelector('[data-fb-shares-tracker=\"1\"]');"
                    "if(!d){var ds=document.querySelectorAll('[role=\"dialog\"]');"
                    "d=ds.length?ds[ds.length-1]:null;}"
                    "return d?d.outerHTML:'';")
                with open(f"debug_dialog_pass{iteration}.html", "w", encoding="utf-8") as fh:
                    fh.write(html or "")
            except Exception:
                pass

        # Update counters.
        # loading_stall: consecutive passes where ONLY skeleton cards appear.
        # If skeletons never resolve, FB requires login to see those shares.
        if new_this_round > 0:
            empty_rounds = 0
            consecutive_loading_stall = 0
        elif loading_this_round > 0:
            # Skeletons present but nothing new — might still be loading
            consecutive_loading_stall += 1
            if consecutive_loading_stall >= MAX_LOADING_STALL:
                print(f"[!] {loading_this_round} share(s) have been stuck loading "
                      f"for {consecutive_loading_stall} passes.")
                print("    Facebook requires you to be logged in to view these shares.")
                print("    Close Chrome, run the script again — your Chrome cookies")
                print("    will be injected automatically.")
                break
        else:
            empty_rounds += 1
            consecutive_loading_stall = 0

        # Hard cap: stop after 5 × MAX_EMPTY_SCROLLS total passes regardless.
        if iteration >= MAX_EMPTY_SCROLLS * 5:
            print("[!] Max total iterations reached. "
                  "If shares are missing, try running while logged in to Chrome.")
            break

        # ── scroll the dialog: JS + Selenium keyboard fallback ────────────
        scrolled = driver.execute_script(JS_SCROLL, SCROLL_STEP_PX)
        # Supplement with a keyboard PAGE_DOWN on the dialog element, which
        # works even when JS scrollTop manipulation is blocked by FB's layout.
        try:
            dlg_el = driver.find_element(By.CSS_SELECTOR, '[data-fb-shares-tracker="1"]')
            ActionChains(driver).move_to_element(dlg_el).click().send_keys(Keys.PAGE_DOWN).perform()
        except Exception:
            pass
        if not scrolled:
            # JS scroll reported nothing moved — try scrolling the active element
            driver.execute_script(
                "var el=document.activeElement;"
                "if(el && el.scrollHeight>el.clientHeight+2) el.scrollTop+=arguments[0];",
                SCROLL_STEP_PX)
        time.sleep(SCROLL_PAUSE)
        iteration += 1

    return all_names


# ---------------------------------------------------------------------------
# Results display
# ---------------------------------------------------------------------------

def build_share_counter(names: list[str]) -> dict[str, int]:
    """Return a {Name: count} dict sorted by count descending."""
    return dict(sorted(Counter(names).items(), key=lambda x: x[1], reverse=True))


def display_results(share_dict: dict[str, int]) -> None:
    """Pretty-print the Name: Counter results."""
    print("\n" + "=" * 50)
    print("  FACEBOOK POST SHARER REPORT")
    print("=" * 50)

    if not share_dict:
        print("  No sharers detected.")
        print("=" * 50)
        return

    col_w = 35
    print(f"  {'Name':<{col_w}} {'Count':>6}")
    print("  " + "-" * (col_w + 8))
    for name, count in share_dict.items():
        print(f"  {name:<{col_w}} {count:>6}")

    print("=" * 50)
    print(f"  Unique sharers  : {len(share_dict)}")
    print(f"  Total shares    : {sum(share_dict.values())}")
    print("=" * 50)


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> None:
    print("=" * 50)
    print("  Facebook Post Sharer Tracker")
    print("=" * 50)

    post_url = POST_URL.strip()
    if not post_url:
        post_url = input("Enter Facebook post URL: ").strip()

    if not post_url.startswith("http"):
        print("[-] Invalid URL. Paste a valid https:// link into POST_URL at the top of this file.")
        sys.exit(1)

    driver = build_driver()
    try:
        # 1. Load the post
        print(f"\n[*] Loading post: {post_url}")
        driver.get(post_url)
        time.sleep(PAGE_LOAD_PAUSE)

        # 2. Dismiss cookie/GDPR consent overlay first (blocks everything underneath)
        consent_found = accept_consent(driver)
        if consent_found:
            # Give the page time to re-render after consent is dismissed
            time.sleep(PAGE_LOAD_PAUSE)
        else:
            print("[*] No consent popup detected.")

        # 3. Save full page HTML for debug inspection
        if DEBUG:
            with open("debug_page.html", "w", encoding="utf-8") as fh:
                fh.write(driver.page_source)
            print("[DEBUG] Saved full page HTML → debug_page.html")

        # 4. Wait for actual post content to be present
        print("[*] Waiting for post content to load...")
        if not wait_for_post_body(driver):
            print("[!] Post body did not appear — the page may be blocked or layout changed.")
            # Save a debug screenshot so user can see what the browser sees
            driver.save_screenshot("debug_screenshot.png")
            print("[!] Saved debug_screenshot.png — open it to see what the browser loaded.")
            sys.exit(1)
        print("[+] Post content loaded.")

        # 5. Click the 'N shares' button
        clicked = click_shares_button(driver)
        if not clicked:
            print("[-] Could not find or click the shares button.")
            print("    Possible reasons: the post has 0 shares, requires login,")
            print("    or Facebook's layout changed.")
            driver.save_screenshot("debug_screenshot.png")
            print("[!] Saved debug_screenshot.png for inspection.")
            sys.exit(1)

        # 6. Find the shares dialog (only called AFTER button was clicked)
        dialog = find_shares_dialog(driver)
        if dialog is None:
            print("[-] Shares dialog did not appear after clicking the button.")
            sys.exit(1)

        print("[+] Shares dialog found. Collecting names...")

        # Dismiss any secondary cookie/login overlay that FB may show
        # anonymously (or to EU users) when the shares dialog opens.
        # Use a short timeout so we don't stall if no overlay appears.
        if accept_consent(driver, timeout=4):
            print("[+] Secondary overlay dismissed — waiting for shares to load.")
            time.sleep(3.0)
        else:
            # Brief pause to let dialog render its initial content
            time.sleep(4.0)

        # 7. Scroll and collect
        names = collect_names_from_dialog(driver, dialog, debug=DEBUG)
        print(f"[+] Done. Collected {len(names)} unique sharer name(s).")

    finally:
        driver.quit()

    # 8. Count and display
    share_dict = build_share_counter(names)
    display_results(share_dict)

    print("\nRaw dict  (Name: Counter):")
    for name, count in share_dict.items():
        print(f"  {name}: {count}")


if __name__ == "__main__":
    main()
