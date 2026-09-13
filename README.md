# rocq-dynamics

Rocq / MathComp formalizations of classical results on opinion dynamics and related
distributed processes, ported from the Lean 4 + Mathlib monorepo
[formal-dynamics/leanamycs](https://github.com/formal-dynamics/leanamycs)
(included read-only as the submodule `reference/leanamycs/`).

| Result | Lean main theorem | Rocq status |
|---|---|---|
| Uniform *push* rumor spreading on `K_n` informs all `n` nodes within `O(log n)` rounds w.h.p. | `RumorPush.push_informs_all_whp` | **proved**: `Dynamics.rumor.main.push_informs_all_whp` |
| 3-majority dynamics reach consensus within `O(log n)` rounds with probability `1 - O(1/n)` from a `60%` majority | `ThreeMajority.majority3_consensus_whp` | **proved**: `Dynamics.majority.main.majority3_consensus_whp` |

Both ports are complete and `Admitted`-free, with the same constants as the Lean
statements; `verify.sh` checks that the main theorems depend only on the three
classical axioms of mathcomp-classical (`boolp`). Both developments sit on a minimal finite-probability layer (uniform averages over
finite types, no measure theory) plus a self-contained Chernoff bound; the Rocq port
keeps that design (`docs/DESIGN.md`).

## Building

Requires Rocq 9.1.x, MathComp 2.5.x, mathcomp-analysis 1.16.x, hierarchy-builder,
algebra-tactics and zify (exact pins and why in `rocq-dynamics.opam`):

```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only ./rocq-dynamics.opam
make -j          # compiles every file in _CoqProject
make gate        # layering check + build + no-Admitted check + axiom audit
./verify.sh      # clean rebuild + Print Assumptions of the headline theorems
```

## Blueprint and documentation

`blueprint/` is a [rocqblueprint](https://github.com/reiniscirpons/rocqblueprint) mirroring
the two Lean blueprints statement for statement (`\rocq{}` tags instead of `\lean{}`);
`.github/workflows/blueprint.yml` builds it (web + pdf) together with the coqdoc API
documentation, checks that every cited declaration exists (`scripts/check_rocq_decls.py`)
and assembles the site under `home_page/`. The assembled site is the `site` artifact of
each run; deployment to GitHub Pages happens automatically once Pages is available for the
repository (it requires the repository to be public on the current plan). Locally:

```bash
uv tool install rocqblueprint          # needs graphviz; xelatex + latexmk for the pdf
cd blueprint/src && rocqblueprint web && rocqblueprint pdf && cd ../..
python3 scripts/check_rocq_decls.py    # after `make`
```

## Layout

```
theories/prelude.v        shared imports, options, smoke lemmas
theories/prob/            finite uniform probability, real inequalities, Chernoff
theories/rumor/           the push protocol                (parallel to majority/)
theories/majority/        the 3-majority process           (parallel to rumor/)
scripts/                  check_layers.py, check_admitted.py, check_rocq_decls.py
blueprint/, home_page/    rocqblueprint sources and the Jekyll landing page
docs/DESIGN.md            representation decisions, Lean -> Rocq dictionary
docs/PLAN.md              milestones, file map, status table
docs/study/               survey of the LLM4Rocq tooling and project conventions
reference/leanamycs/      the Lean source (git submodule, read-only)
```

## Working with AI agents

This project is developed with Claude Code and the tools of
[LLM4Rocq](https://github.com/LLM4Rocq): the `rocq-mcp` MCP server (interactive goals via
petanque), the `rocq` plugin (`/rocq:prove`, `/rocq:autoprove`, `/rocq:checkpoint`) and
the `mathcomp-skills` plugin (MathComp style guide, `/mathcomp-review`). They are
installed at user level; `docs/study/llm4rocq-tooling.md` §4 has the exact commands,
and `CLAUDE.md` the working rules. A collaborator without the user-level setup can
register the MCP server for this repo only:

```bash
uv tool install "git+https://github.com/LLM4Rocq/rocq-mcp"
claude mcp add --scope project rocq-mcp -- opam exec --switch=rocq-9.1.1 -- rocq-mcp
```
