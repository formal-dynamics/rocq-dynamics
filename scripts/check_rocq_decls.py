#!/usr/bin/env python3
"""Check that every Rocq declaration cited by the blueprint exists.

`rocqblueprint web` (plasTeX) writes `blueprint/rocq_decls`, one fully qualified
name per line, collected from the `\\rocq{...}` tags of blueprint/src/content.tex.
This script turns that list into a probe file of `Check` commands and runs it
against the compiled theories, so a renamed or deleted declaration fails the
build instead of silently producing a dangling link (the Rocq analogue of
leanblueprint's `checkdecls`).

Notation abbreviations cannot be `Check`ed bare; NOTATIONS maps them to a
sample application.

Usage: python3 scripts/check_rocq_decls.py [blueprint/rocq_decls]
Requires the project to be built (`make`) and `rocq` on PATH.
"""
from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

NOTATIONS = {
    "Dynamics.rumor.model.Tgt": "(Dynamics.rumor.model.Tgt 2)",
    "Dynamics.majority.model.Tgt3": "(Dynamics.majority.model.Tgt3 2)",
}


def main() -> int:
    decls_path = Path(sys.argv[1] if len(sys.argv) > 1 else "blueprint/rocq_decls")
    if not decls_path.exists():
        print(f"check_rocq_decls: {decls_path} not found (run `rocqblueprint web` first)")
        return 1
    decls = sorted({d.strip() for d in decls_path.read_text().splitlines() if d.strip()})
    if not decls:
        print("check_rocq_decls: no declarations listed"); return 1

    modules = sorted({".".join(d.split(".")[:-1]) for d in decls})
    lines = ["From Dynamics Require Import prelude."]
    lines += [f"From {'.'.join(m.split('.')[:-1])} Require Import {m.split('.')[-1]}." for m in modules]
    for d in decls:
        lines.append(f"Check {NOTATIONS.get(d, d)}.")
    with tempfile.NamedTemporaryFile("w", suffix=".v", delete=False) as f:
        f.write("\n".join(lines) + "\n"); probe = f.name
    try:
        r = subprocess.run(
            ["rocq", "repl", "-q", "-w", "none", "-R", "theories", "Dynamics", "-batch", "-l", probe],
            capture_output=True, text=True)
    finally:
        Path(probe).unlink(missing_ok=True)
    out = r.stdout + r.stderr
    if r.returncode != 0 or "Error" in out:
        print(out)
        print(f"check_rocq_decls: FAILED ({len(decls)} declarations checked)")
        return 1
    print(f"check_rocq_decls: OK ({len(decls)} declarations exist)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
