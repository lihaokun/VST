#!/usr/bin/env python3
"""Regenerate/check the candidate's canonical public-library source inventory."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
NAMES = sorted(("FusionExact", "FusionExactSem", "FusionMemvals", "FusionViews64",
                "FusionStore", "SeparationLogicAsLogic", "SeparationLogicAsLogicSoundness"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = "".join(f"{hashlib.sha256((ROOT / ('floyd/' + name + '.v')).read_bytes()).hexdigest()}  floyd/{name}.v\n"
                      for name in NAMES)
    digest = hashlib.sha256(content.encode()).hexdigest()
    path = ROOT / "fusion/release.json"
    metadata = json.loads(path.read_text())
    if args.check:
        if ((ROOT / "fusion/payload.sha256").read_text() != content
                or metadata["patch_sha256"] != digest):
            raise SystemExit("Source inventory changed; update and review the candidate manifest")
    else:
        (ROOT / "fusion/payload.sha256").write_text(content)
        metadata["patch_sha256"] = digest
        path.write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n")
    print(f"Candidate payload: {digest}")


if __name__ == "__main__":
    main()
