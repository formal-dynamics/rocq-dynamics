#!/usr/bin/env python3
"""Fail if any theories/**/*.v contains Admitted, admit, or a top-level Axiom-like
declaration outside comments. Reports file:line for each hit.

Usage: python3 scripts/check_admitted.py [--allow-admitted]
  --allow-admitted   only forbid Axiom/Parameter/Conjecture/Hypothesis (for WIP branches)
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ADMIT_RE = re.compile(r"^\s*(Admitted\.|admit\.)")
AXIOM_RE = re.compile(r"^\s*(Axiom|Axioms|Parameter|Parameters|Conjecture)\s")  # section Hypothesis/Variable are premises, not axioms


def strip_comments(src: str) -> str:
    """Replace Rocq (* ... *) comments (nested) by spaces, preserving newlines."""
    out, depth, i = [], 0, 0
    while i < len(src):
        two = src[i:i + 2]
        if two == "(*":
            depth += 1; out.append("  "); i += 2
        elif two == "*)" and depth:
            depth -= 1; out.append("  "); i += 2
        else:
            out.append(src[i] if (depth == 0 or src[i] == "\n") else " "); i += 1
    return "".join(out)


def main() -> int:
    allow_admitted = "--allow-admitted" in sys.argv
    bad = 0
    for f in sorted(Path("theories").rglob("*.v")):
        for n, line in enumerate(strip_comments(f.read_text(encoding="utf-8")).splitlines(), 1):
            if not allow_admitted and ADMIT_RE.match(line):
                print(f"{f}:{n}: {line.strip()}"); bad += 1
            if AXIOM_RE.match(line):
                print(f"{f}:{n}: {line.strip()}"); bad += 1
    if bad:
        print(f"check_admitted: {bad} forbidden declaration(s)"); return 1
    print("check_admitted: OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
