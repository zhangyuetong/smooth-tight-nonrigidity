"""Rebuild the active ver503 blueprint from a current local kernel audit."""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]


def main():
    target = json.loads((ROOT / "target-lock.json").read_text(encoding="utf-8"))["target"]
    if target != "ver503":
        raise SystemExit(f"Unsupported active manuscript target: {target}")
    from ver503_blueprint import main as active_main
    active_main()


if __name__ == "__main__":
    main()
