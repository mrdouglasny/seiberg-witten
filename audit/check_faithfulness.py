#!/usr/bin/env python3
"""Verify FAITHFULNESS.md's Lean quotes verbatim against the source tree.

The faithfulness digest pairs each informal claim with a quoted Lean statement.
The informal <-> formal comparison is the human reviewer's job; this script does
the machine half: every ```lean block that follows a `**Formal** (`<path>`)` line
must appear verbatim (whitespace-normalized) in that file, so the digest cannot
drift from the code. Companion to gen_axiom_report.sh (which pins the axiom
footprints quoted in the same file).

Usage: python3 audit/check_faithfulness.py   (from the repo root or audit/)
Exit: 0 if every quote matches, 1 otherwise.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DIGEST = ROOT / "audit" / "FAITHFULNESS.md"

# `**Formal** (`path`)...:` optionally followed by prose, then one or more
# ```lean ... ``` blocks before the next entry.
ENTRY_RE = re.compile(
    r"\*\*Formal\*\*\s*\(`([^`]+)`[^)]*\)[^\n]*\n(.*?)(?=\n## |\n\*\*Formal\*\*|\n\*\*`|\Z)",
    re.DOTALL,
)
BLOCK_RE = re.compile(r"```lean\n(.*?)```", re.DOTALL)


def norm(s: str) -> str:
    return " ".join(s.split())


def main() -> int:
    text = DIGEST.read_text(encoding="utf-8")
    failures, checked = [], 0
    entries = ENTRY_RE.findall(text)
    if not entries:
        print("ERROR: no `**Formal** (`<path>`)` entries found in FAITHFULNESS.md")
        return 1
    for relpath, body in entries:
        src_file = (ROOT / relpath).resolve()
        if not src_file.exists():
            if relpath.startswith("../"):
                # quote from a sibling dependency (e.g. jacobian-challenge);
                # checkable only when that repo is present (cf. BUILD.md)
                print(f"  SKIP {relpath}: dependency not checked out")
                continue
            failures.append(f"{relpath}: file does not exist")
            continue
        src = norm(src_file.read_text(encoding="utf-8"))
        blocks = BLOCK_RE.findall(body)
        if not blocks:
            failures.append(f"{relpath}: entry has no ```lean block")
            continue
        for block in blocks:
            checked += 1
            head = block.strip().splitlines()[0].strip()
            if norm(block) in src:
                print(f"  ok  {relpath}: {head[:70]}")
            else:
                failures.append(f"{relpath}: quote drifted from source: {head[:70]}")
    print(f"\n{checked} Lean quotes checked against source.")
    if failures:
        print("FAILURES:")
        for f in failures:
            print(f"  ✗ {f}")
        print("Fix FAITHFULNESS.md (or the source moved); quotes must match verbatim.")
        return 1
    print("✓ FAITHFULNESS.md quotes are in sync with the source tree.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
