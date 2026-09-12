# Changelog

## Unreleased

### M0 — toolchain and skeleton (2026-09-10)
- Studied the LLM4Rocq tooling and project conventions (`docs/study/`).
- Chose the LLM4Rocq toolchain snapshot: Rocq 9.1.1, MathComp 2.5.0, mathcomp-analysis
  1.16.0, HB 1.10.2, algebra-tactics 1.2.7, coq-lsp 0.2.5+9.1 (`rocq-dynamics.opam`).
- Repo skeleton: `_CoqProject`, `Makefile` (generates `CoqMakefile`), `verify.sh`,
  `scripts/check_layers.py`, `scripts/check_admitted.py`, CI `build.yml`,
  `theories/prelude.v` with smoke lemmas, `CLAUDE.md`, `docs/DESIGN.md`, `docs/PLAN.md`.
- Added `reference/leanamycs` (the Lean source) as a read-only submodule.
- M0 verified 2026-09-11: `make`, `./verify.sh` (only the three `boolp` axioms) and
  `make gate` pass; `rocq-mcp` health and `rocq_query` verified against the switch.
