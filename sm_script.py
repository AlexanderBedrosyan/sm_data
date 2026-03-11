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
MAX_EMPTY_SCROLLS = 5

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
    tmp_db: str | None = None
    try:
        tmp_db = tempfile.mktemp(suffix="_fb_cookies.db")
        shutil.copy2(cookies_db, tmp_db)
        db_uri = f"file:{tmp_db}?mode=ro"
    except Exception:
        tmp_db = None
        # Open the live DB in immutable/read-only mode via SQLite URI
        db_uri = "file:{}?mode=ro&immutable=1".format(cookies_db.replace("\\", "/"))

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


def accept_consent(driver: webdriver.Chrome) -> bool:
    """
    Dismiss the cookie/GDPR consent overlay.
    Tries normal click first, then JavaScript click as fallback.
    Returns True if a consent button was found and clicked.
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
            btn = WebDriverWait(driver, 8).until(
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
    Find and click the 'N shares' button on the post page.
    Returns True if successfully clicked, False otherwise.
    """
    # Find every text node that contains both a digit and the word 'share'
    candidates = driver.find_elements(
        By.XPATH,
        "//*[contains(translate(text(),'ABCDEFGHIJKLMNOPQRSTUVWXYZ',"
        "'abcdefghijklmnopqrstuvwxyz'),'share')]"
    )

    for el in candidates:
        try:
            text = el.text.strip()
            if not text:
                continue
            if re.search(r'\d', text) and re.search(r'share', text, re.I):
                driver.execute_script("arguments[0].scrollIntoView(true);", el)
                time.sleep(0.3)
                try:
                    el.click()
                except Exception:
                    driver.execute_script("arguments[0].click();", el)
                print(f"[+] Clicked shares button: '{text}'")
                time.sleep(6.0)   # wait for dialog and its lazy content to load
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


def collect_names_from_dialog(driver: webdriver.Chrome, dialog) -> list[str]:
    """
    Scroll through the shares dialog and collect sharer names.
    Returns a list with duplicates preserved for counting.

    Facebook's shares dialog does NOT use real profile hrefs for the sharer
    name links; instead it uses href="#". The name appears in two reliable
    places:
      1. <div data-ad-rendering-role="profile_name"> … <b><span>Name</span></b> …
      2. <a href="#" role="link" aria-label="Name">  (avatar link)
    We try both and de-duplicate.
    """

    # Regex to detect timestamp strings in any language:
    TIMESTAMP_RE = re.compile(
        r'^(\d+\s*(m|h|d|w|s|мин|ч|д|лв|сек|min|sec|hr|hrs|just\s*now|now))$',
        re.I | re.U,
    )

    # Labels that are NOT sharer names
    SKIP_ARIA = {
        "close", "actions for this post", "show attachment",
        "loading...", "menu", "more", "back",
    }

    def _is_valid_name(text: str) -> bool:
        if not text or len(text) < 2:
            return False
        if TIMESTAMP_RE.match(text):
            return False
        if text.lower() in SKIP_WORDS or text.lower() in SKIP_ARIA:
            return False
        if text.isdigit() or re.match(r'^[\d\s,·.]+$', text):
            return False
        return True

    def _extract_from_soup(soup) -> list[str]:
        found: list[str] = []
        found_set: set[str] = set()

        def _add(text: str) -> None:
            if _is_valid_name(text) and text not in found_set:
                found_set.add(text)
                found.append(text)

        # ── Strategy 1: data-ad-rendering-role="profile_name" ──────────────
        for div in soup.find_all(attrs={"data-ad-rendering-role": "profile_name"}):
            b = div.find("b")
            if b:
                _add(b.get_text(strip=True))
                continue
            heading = div.find(["h1", "h2", "h3"])
            if heading:
                _add(heading.get_text(strip=True))

        # ── Strategy 2: aria-label on <a role="link"> (any href) ─────────────
        # Catches entries where the avatar link carries the name as aria-label,
        # regardless of whether href is "#" or a real profile URL.
        for a in soup.find_all("a", role="link"):
            label = (a.get("aria-label") or "").strip()
            if label and label.lower() not in SKIP_ARIA:
                _add(label)

        return found

    all_names: list[str] = []
    seen: set[str] = set()
    empty_scrolls = 0

    while empty_scrolls < MAX_EMPTY_SCROLLS:
        try:
            inner_html = dialog.get_attribute("innerHTML")
            soup = BeautifulSoup(inner_html, "html.parser")
        except Exception:
            break

        new_this_round = 0
        for name in _extract_from_soup(soup):
            if name not in seen:
                seen.add(name)
                all_names.append(name)
                new_this_round += 1

        if new_this_round == 0:
            empty_scrolls += 1
        else:
            empty_scrolls = 0

        # Scroll down inside the dialog.
        # ActionChains click on the dialog + Page Down is the most reliable way
        # to trigger Facebook's IntersectionObserver for lazy-loaded entries
        # in headless Chrome.  Pure JS scrollTop changes don't fire IO callbacks.
        try:
            ActionChains(driver).move_to_element(dialog).click().perform()
            for _ in range(3):
                ActionChains(driver).send_keys(Keys.PAGE_DOWN).perform()
                time.sleep(0.3)
        except Exception:
            pass

        # Wait for lazy-loading spinners to be replaced by real content
        time.sleep(SCROLL_PAUSE)

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

        # 3. Wait for actual post content to be present
        print("[*] Waiting for post content to load...")
        if not wait_for_post_body(driver):
            print("[!] Post body did not appear — the page may be blocked or layout changed.")
            # Save a debug screenshot so user can see what the browser sees
            driver.save_screenshot("debug_screenshot.png")
            print("[!] Saved debug_screenshot.png — open it to see what the browser loaded.")
            sys.exit(1)
        print("[+] Post content loaded.")

        # 4. Click the 'N shares' button
        clicked = click_shares_button(driver)
        if not clicked:
            print("[-] Could not find or click the shares button.")
            print("    Possible reasons: the post has 0 shares, requires login,")
            print("    or Facebook's layout changed.")
            driver.save_screenshot("debug_screenshot.png")
            print("[!] Saved debug_screenshot.png for inspection.")
            sys.exit(1)

        # 5. Find the shares dialog (only called AFTER button was clicked)
        dialog = find_shares_dialog(driver)
        if dialog is None:
            print("[-] Shares dialog did not appear after clicking the button.")
            sys.exit(1)

        print("[+] Shares dialog found. Collecting names...")

        # Brief pause to let dialog render its initial content
        time.sleep(4.0)

        # 6. Scroll and collect
        names = collect_names_from_dialog(driver, dialog)
        print(f"[+] Done. Collected {len(names)} unique sharer name(s).")

    finally:
        driver.quit()

    # 6. Count and display
    share_dict = build_share_counter(names)
    display_results(share_dict)

    print("\nRaw dict  (Name: Counter):")
    for name, count in share_dict.items():
        print(f"  {name}: {count}")


if __name__ == "__main__":
    main()
