"""
Blockline - Entry point

Loads the block modules and starts the visual editor UI.
"""

import os
import shutil
import sys

from ui import start_ui
from engine.loader import load_blocks_from_folder


def get_bundle_path():
    """
    Where the app's bundled default assets live: PyInstaller's
    temporary extraction directory when running as a built .exe or
    AppImage (sys._MEIPASS), or this script's own folder when running
    from source with `python main.py`.
    """
    if getattr(sys, "frozen", False) and hasattr(sys, "_MEIPASS"):
        return sys._MEIPASS
    return os.path.dirname(os.path.abspath(__file__))


def get_persistent_data_path():
    """
    Where user data actually lives - languages, custom blocks, saves,
    settings. Always next to the real executable/script, NEVER inside
    PyInstaller's bundle extraction folder: that folder is temporary
    and gets deleted the moment the app closes, which would silently
    discard anything created while running a built .exe/AppImage
    (new languages, custom blocks, etc.) with no warning.
    """
    if getattr(sys, "frozen", False):
        return os.path.dirname(os.path.abspath(sys.executable))
    return os.path.dirname(os.path.abspath(__file__))


def ensure_languages_available():
    """
    On first run of a frozen build, copy the bundled default
    languages/ folder out to a persistent location next to the actual
    exe/AppImage. After that, always use the persistent copy - it's
    both usable immediately (ships with Python/C++ etc. blocks) and
    safe to edit or add to, since edits there survive restarts.
    """
    persistent_languages = os.path.join(get_persistent_data_path(), "languages")

    if not os.path.isdir(persistent_languages):
        bundled_languages = os.path.join(get_bundle_path(), "languages")
        if os.path.isdir(bundled_languages):
            shutil.copytree(bundled_languages, persistent_languages)
            print(f"First run: copied default languages to {persistent_languages}")

    return persistent_languages


LANGUAGES_PATH = ensure_languages_available()
BLOCKS_PATH = os.path.join(LANGUAGES_PATH, "python", "blocks")


def main():
    print("Starting Blockline...")
    print(f"Languages folder: {LANGUAGES_PATH}")

    blocks = load_blocks_from_folder(BLOCKS_PATH)

    if not blocks:
        print(f"⚠ No blocks found under '{BLOCKS_PATH}'.")
        print("  Check that the folder exists and contains block files")
        print("  with a 'block_id' attribute.")
    else:
        print(f"Loaded {len(blocks)} block(s):")
        for block_id, module in blocks.items():
            display_name = getattr(module, "display_name", "Unknown")
            print(f" - {block_id} ({display_name})")

    start_ui(blocks, languages_path=LANGUAGES_PATH)


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print(f"✗ Blockline failed to start: {e}", file=sys.stderr)
        sys.exit(1)
