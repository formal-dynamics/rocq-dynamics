#!/usr/bin/env python3
"""Import-layer checker for rocq-dynamics (pattern borrowed from LLM4Rocq/icones-rocq).

theories/ is stratified:

    0  prelude              shared imports, options, smoke lemmas
    1  prob                 finite uniform probability, real inequalities, Chernoff
    2  rumor | majority     the two processes (parallel: neither imports the other)

A file may only `Require` files whose directory has a rank <= its own, and
never a *different* directory of the same rank. Intra-directory cycles are
already caught by coqdep.

Usage: python3 scripts/check_layers.py [--list] [--graph]
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

LAYERS: list[tuple[str, ...]] = [
    ("prelude",),
    ("prob",),
    ("rumor", "majority"),
]
RANK = {d: i for i, ds in enumerate(LAYERS) for d in ds}
ROOT_NS = "Dynamics"

REQ_RE = re.compile(
    r"^\s*From\s+" + ROOT_NS + r"(?:\.(\S+))?\s+Require(?:\s+(?:Import|Export))?\s+([^.]+)\.",
    re.M,
)


def layer_of(path: Path, theories: Path) -> str:
    rel = path.relative_to(theories)
    return rel.parts[0] if len(rel.parts) > 1 else "prelude"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--graph", action="store_true")
    a = ap.parse_args()
    theories = Path(a.root) / "theories"
    files = sorted(theories.rglob("*.v"))
    bad = 0
    for f in files:
        me = layer_of(f, theories)
        if me not in RANK:
            print(f"{f}: directory '{me}' is not a known layer"); bad += 1
            continue
        if a.list:
            print(f"{RANK[me]}  {me:10s} {f}")
        for m in REQ_RE.finditer(f.read_text(encoding="utf-8")):
            prefix, mods = m.group(1), m.group(2).split()
            for mod in mods:
                parts = (prefix.split(".") if prefix else []) + mod.split(".")
                dep = parts[0] if len(parts) > 1 else "prelude"
                if a.graph:
                    print(f"{me} -> {dep}   ({f.name} requires {'.'.join(parts)})")
                if dep not in RANK:
                    print(f"{f}: requires unknown layer '{dep}'"); bad += 1
                elif RANK[dep] > RANK[me]:
                    print(f"{f}: layer '{me}' (rank {RANK[me]}) imports higher layer '{dep}'"); bad += 1
                elif RANK[dep] == RANK[me] and dep != me:
                    print(f"{f}: parallel layers '{me}' and '{dep}' must not import each other"); bad += 1
    if bad:
        print(f"check_layers: {bad} violation(s)"); return 1
    print(f"check_layers: OK ({len(files)} files)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
