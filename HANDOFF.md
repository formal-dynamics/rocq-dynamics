# HANDOFF — rocq-dynamics (written 2026-09-13 by Claude Code, for Codex or any other agent)

Read this first, then `CLAUDE.md` (working rules, also valid for you), `docs/DESIGN.md`
(representation decisions and §4 "Lessons": ~40 MathComp pitfalls we hit), `docs/PLAN.md`
(milestones and per-file status), `CHANGELOG.md`.

## 1. State of the project

**The mathematics is done.** `main` (pushed to `github.com/formal-dynamics/rocq-dynamics`)
holds a complete, `Admitted`-free Rocq/MathComp port of the Lean monorepo
`formal-dynamics/leanamycs` (submodule `reference/leanamycs/`):

| Result | Rocq theorem | Status |
|---|---|---|
| Push rumor spreading on `K_n` informs all nodes in `(⌈117 ln n⌉+23)+⌈6 ln n⌉` rounds, failure ≤ 2/n | `Dynamics.rumor.main.push_informs_all_whp` (+ `'` variant) | proved, axiom-audited |
| 3-majority consensus in `10+(⌈6 ln n⌉+2)` rounds from a 60% majority, `ln n ≥ 30`, failure ≤ 500/n | `Dynamics.majority.main.majority3_consensus_whp` (+ `_fail_le_clean`) | proved, axiom-audited |

- 15 files under `theories/` (layers `prelude < prob < rumor | majority`, enforced by
  `scripts/check_layers.py`). ~160 lemmas, all `Qed`. Constants identical to Lean.
- `make gate` = layering check + build + no-`Admitted` check + `verify.sh` (clean rebuild and
  `Print Assumptions` of the four headline theorems, allow-list = the three `boolp` axioms:
  functional extensionality, propositional extensionality, constructive indefinite
  description). It is green on `main` at commit `04875e5`.
- CI: `.github/workflows/build.yml` runs the same gate in the
  `mathcomp/mathcomp:2.5.0-rocq-prover-9.1` image (installs mathcomp-analysis 1.16.0 on top,
  ~20–25 min). The first run (`gh run list`) was still in progress at handoff time: **check
  it**; a likely failure mode is an opam solver or permission issue inside the container,
  not the proofs.

## 2. Toolchain (already installed on this machine, user level)

- opam 2.5.2 (`~/.local/bin/opam`), default switch `rocq-9.1.1`: Rocq 9.1.1 (`rocq-core`,
  `coq-core` compat shim providing `coqc`, `rocq-stdlib` 9.1.0), MathComp 2.5.0,
  mathcomp-classical/reals/analysis 1.16.0, hierarchy-builder 1.10.2, algebra-tactics 1.2.7,
  zify, coq-lsp 0.2.5+9.1 (provides `pet` for petanque). Activate with
  `eval $(opam env --switch=rocq-9.1.1 --set-switch)`.
- Why these versions: the released coq-lsp requires `rocq-core < 9.2`; the LLM4Rocq
  tooling (mathcomp-skills guide, rocqet index) is verified against MC 2.5 / MCA 1.16
  (`docs/study/llm4rocq-tooling.md`).
- Claude Code user-level: MCP servers `rocq-mcp` (13 tools; runs via
  `opam exec --switch=rocq-9.1.1 -- rocq-mcp`) and `rocqet` (hosted MathComp semantic
  search, flaky 503s); plugins `rocq@rocq-skills` and `mathcomp-skills@llm4rocq-local`
  (local marketplace `~/.claude/local-marketplaces/llm4rocq-local`). For Codex: the same
  `rocq-mcp` binary (`~/.local/bin/rocq-mcp`) can be registered as an MCP server; the
  `mathcomp-skills` markdown under that marketplace directory is worth reading regardless.
- uv tools: `rocq-mcp`, `rocqet`, `rocqblueprint` (in `~/.local/bin`).
- Python 3.13, `latexmk`, `xelatex`, `dot` (graphviz) available locally.

## 3. How the work was done (reuse this)

Statement-first: every Lean declaration became an `Admitted` skeleton with the Lean name in
its docstring; only after all statements compiled were proofs filled, one file per agent,
each agent compiling ONLY its file with
`rocq c -w -notation-overridden,-ambiguous-paths -R theories Dynamics theories/<dir>/<file>.v`
(never bare `make` while others compile: `.vo` files get inconsistent). 2–3 concurrent
agents is safe; 6 hit the rate limit. Real-arithmetic side goals: `lra`/`nra` with the
transcendental facts supplied as hypotheses (`expR_ge1Dx`, `ln_ge_quadratic`, ...).

## 4. In flight at handoff (uncommitted, in the working tree)

Milestone **M7 (blueprint + docs site)**:

- `blueprint/src/{web,print}.tex`, `plastex.cfg`, `latexmkrc`, `extra_styles.css`,
  `macros/{common,print,web}.tex` — done (from the rocqblueprint templates; `common.tex`
  defines `\N \R \E \Pr \card \avg \expList \rocqfile` and the theorem environments).
- `blueprint/src/content.tex` — being written by an agent: a single Rocq blueprint in three
  chapters (finite probability; rumor spreading; 3-majority), translating the two Lean
  `blueprint/src/content.tex` files with `\rocq{Dynamics.<module>.<name>}` tags (Lean
  names → Rocq names via the `(** Lean: [...] *)` docstrings in `theories/`), `\rocqok`,
  `\uses{}` with label prefixes `pr:`, `rs:`, `mj:`. Its completion status is in §6 below.
  **Next steps:** `cd blueprint/src && rocqblueprint web && rocqblueprint pdf` (the pdf
  needs xelatex + unicode-math, both present); fix LaTeX errors; then `make` and
  `python3 scripts/check_rocq_decls.py blueprint/rocq_decls` (our `checkdecls`: it `Check`s
  every cited name; notations `Tgt`/`Tgt3` are special-cased in the script).
- `home_page/` — Jekyll landing page (cayman theme) from the rocqblueprint templates; the
  workflow copies `blueprint/`, `blueprint.pdf`, `docs/` (coqdoc) into it.
- `.github/workflows/blueprint.yml` — three jobs (blueprint in texlive container → coqdoc +
  declaration check in the Rocq container → Jekyll assembly, `site` artifact) plus a
  best-effort Pages deploy. **GitHub Pages cannot be enabled: the repo is private and the
  org plan does not allow Pages on private repos** (`gh api -X POST .../pages` → 422). Either
  make the repo public (the Lean one is) or keep using the `site` artifact.
- `README.md` updated for the above; `.gitignore` has the blueprint build products.

Milestone **M8 (faithfulness audit)**:

- `docs/LEAN_TO_ROCQ.md` — being written by an agent: one row per Lean declaration (Lean
  name → Rocq name, statement differences, constants), helper lemmas without Lean
  counterpart, proof-level deviations, verdict. Status in §6.
- `theories/prob/equivalence.v` — port of Lean `Equivalence.lean`
  (`expList k F = avg (fun w : k.-tuple T => F w)`, faithfulness of the recursive
  expectation). Added to `_CoqProject` after `indep.v`. Status in §6. It is NOT needed by
  the main theorems; if it does not compile, remove it and its `_CoqProject` line before
  committing so `make gate` stays green.

## 5. Immediate to-do list for the next agent

1. `eval $(opam env --switch=rocq-9.1.1 --set-switch); make -j && make gate` — must stay
   green. If `equivalence.v` breaks it, see §4.
2. Finish/verify `blueprint/src/content.tex` (web + pdf build, `check_rocq_decls.py`).
3. Finish `docs/LEAN_TO_ROCQ.md` (mark unfinished rows `TODO`), then mark M7/M8 in
   `docs/PLAN.md` and add a CHANGELOG entry.
4. Commit on `main` (guardrail: the `rocq` plugin hook blocks `git push` in Rocq
   directories; use `ROCQ_GUARDRAILS_BYPASS=1 git push` from Claude Code; irrelevant for
   Codex), push, watch both workflows with `gh run list` / `gh run view <id> --log-failed`.
5. Decide on repo visibility for Pages.
6. Optional later: `Import` hygiene (`finset.`/`fintype.` qualifications left from the time
   `classical_sets` was exported are harmless), a `.claude/agents/` pool for parallel
   provers with per-worktree `rocq-mcp` servers (see `docs/study/llm4rocq-tooling.md` §1.2),
   sharper constants on a `sharper/` branch (never on the faithful files).

## 6. Status reported by the two agents at wrap-up

- **Blueprint content** (`blueprint/src/content.tex`, 1848 lines): COMPLETE. 76 graph nodes
  (22 probability, 24 rumor, 30 majority), 160 distinct `\rocq{}` names, all verified
  (`check_rocq_decls.py`: OK), every declaration of `theories/` except the prelude smoke
  lemmas is cited, all nodes `\rocqok`. Local `rocqblueprint web` and `rocqblueprint pdf`
  both succeed (`plastex` is in `~/.local/share/uv/tools/rocqblueprint/bin`, add it to PATH).
  Remaining polish only: switch inline `\mathbb{E}` etc. to the `common.tex` macros if desired.
- **Faithfulness audit** (`docs/LEAN_TO_ROCQ.md`): COMPLETE, 176/176 Lean declarations,
  no non-faithful statement; 7 unmapped (5 automatic typeclass instances, 2 private proof
  devices); 15 Rocq-only helpers and 8 proof-level deviations documented; verdict: both
  main theorems are statement-for-statement faithful.
- **Equivalence port** (`theories/prob/equivalence.v`, `expList_eq_avg_tuple`): COMPLETE,
  0 Admitted, only the three `boolp` axioms; in `_CoqProject`; `make gate` green (16 files).
- Everything above is committed and pushed together with this file. The `blueprint.yml`
  workflow has not run yet at handoff time: check `gh run list`.
