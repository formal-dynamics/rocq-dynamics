# Changelog

## Unreleased

### M7 — blueprint and documentation site (2026-09-13)
- `blueprint/` (rocqblueprint, 76 nodes mirroring both Lean blueprints, all proved),
  `home_page/` (Jekyll), `scripts/check_rocq_decls.py` (the `checkdecls` analogue),
  `.github/workflows/blueprint.yml` (web + pdf + coqdoc + declaration check, `site`
  artifact; Pages deploy best-effort — Pages is unavailable while the repo is private).
- `HANDOFF.md` for the next agent.

### M8 — faithfulness audit and `Equivalence.lean` (2026-09-13)
- `docs/LEAN_TO_ROCQ.md`: every Lean declaration of both projects (176) mapped to its
  Rocq counterpart with the exact statement differences (representation changes only:
  `Finset`→`{set _}`, `Fin n`→`'I_n`, `List`→`seq`, `if P then 1 else 0`→`(P)%:R`,
  `Nat.ceil`→`ceiln`, `Nonempty`→`(0 < #|T|)%N`, Prop→bool); no hypothesis or constant
  differs. Rocq-only helpers and proof-level deviations listed with justifications.
- `theories/prob/equivalence.v`: `expList_eq_avg_tuple` — `expList k F` equals the uniform
  average of `F` over the product space `k.-tuple T` (Lean `expList_eq_avg_ofFn`, with
  `k.-tuple T`/`tval` for `Fin k → α`/`List.ofFn` and `cons_tuple` for `Fin.consEquiv`);
  helpers `avg_pair` (Fubini for `avg`) and `cons_tuple_bij`. Only the three `boolp` axioms.

### M1–M6 — both formalizations complete (2026-09-12, branch prob-layer)
- All 15 files Admitted-free; `verify.sh` audits `push_informs_all_whp`,
  `push_informs_all_whp'`, `majority3_consensus_whp`, `majority3_consensus_fail_le_clean`:
  only the three `boolp` axioms. Constants identical to the Lean statements.
- Deviations from the Lean proofs (constant-neutral, documented in the files): numerics avoid
  `11!` (large literals overflow) via degree-14/5 Taylor terms; `saturation.v` adds an
  MVT-based Padé bound `ln_ge_pade` that MathComp-Analysis lacks; `ln 2 <= 7/10` from
  `expR_ge_series`; stage 2b avoids `ln 75000` via `75000 L^2 <= L^6`.

### M1/M2 — probability layer (2026-09-12, branch prob-layer)
- `theories/prob/{avg,indep,bounds,chernoff}.v`: every declaration of the Lean `Prob`,
  `Bounds` and `Chernoff` files as statements; `avg`, `indep`, `chernoff` fully proved
  (`bounds` in progress). `bigA_distr_bigA` replaces Lean's hand-rolled independence.

### M3/M5 — process statements (2026-09-12, branch prob-layer)
- `theories/rumor/*.v` and `theories/majority/*.v`: all definitions and theorem
  statements of both Lean projects as `Admitted` skeletons, same constants as Lean.
  `Tgt n` is a dependent finfun; `Tgt3 n` a finfun into right-nested triples.

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
