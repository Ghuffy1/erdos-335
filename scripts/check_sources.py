"""Check every released proof source against the completed verification run."""

import hashlib
import json
from pathlib import Path


def main():
    root = Path(__file__).resolve().parent.parent
    manifest = json.loads((root / "verification/source-snapshot.json").read_text(encoding="utf-8"))
    for relative, expected in manifest["files"].items():
        path = root / relative
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise SystemExit(f"Source mismatch: {relative}")
    sources = set()
    for folder in [root / "Erdos335", root / "MiscYD"]:
        sources.update(str(path.relative_to(root)).replace("\\", "/") for path in folder.rglob("*.lean"))
    sources.update(path.name for path in root.glob("*.lean"))
    expected_sources = {path for path in manifest["files"] if path.endswith(".lean")}
    if sources != expected_sources:
        raise SystemExit("The released canonical source set differs from the verified source set.")
    print(f"PASS: {len(expected_sources)} Lean files and all pinned supporting source files match.")


if __name__ == "__main__":
    main()
