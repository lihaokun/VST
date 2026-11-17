#!/usr/bin/env python3
"""Read the ClightForge export configuration for Make (not an identity verifier)."""
import json
from pathlib import Path
import re
import sys

try:
    root = Path(sys.argv[1])
    if not re.fullmatch(r"[A-Za-z0-9_./-]+", str(root)):
        raise ValueError("component path must be usable in Make load-path flags")
    record = json.loads((root / "semantics.json").read_text())
    if (record["schema"], record["kind"]) != ("clightforge.identity.v1", "semantics"):
        raise ValueError("expected a semantics component")
    content = record["content"]
    facts = content["facts"]
    if (content["profile"], content["system"], content["semantic_version"], facts["arch"],
        facts["model"], facts["abi"], facts["ptr64"], facts["big_endian"],
        facts["align_int64"], facts["align_float64"]) != (
            "x86_64-linux", "linux", "3.17", "x86", "64", "standard", True, False, 8, 8):
        raise ValueError("unsupported semantics profile/layout/version")
    for module in content["modules"]:
        for field in ("source", "object"):
            if not (root / module[field]).is_file():
                raise ValueError("missing component file: " + module[field])
    print(content["semantic_version"], facts["arch"], facts["model"])
except (OSError, ValueError, KeyError, IndexError, TypeError) as error:
    sys.exit("ClightForge semantics configuration: " + str(error))
