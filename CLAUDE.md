# rocq-dynamics — instructions for coding agents

Rocq/MathComp port of the Lean 4 + Mathlib monorepo
[formal-dynamics/leanamycs](https://github.com/formal-dynamics/leanamycs)
(checked out read-only at `reference/leanamycs/`): two `sorry`-free
formalizations of opinion dynamics on the complete graph,

- **rumor spreading** (uniform push): from one informed node, all `n` nodes are
  informed after `O(log n)` rounds with probability `>= 1 - 2/n`
  (`RumorPush.push_informs_all_whp`);
- **3-majority**: from a `60%` majority, consensus after `O(log n)` rounds with
  probability `>= 1 - 500/n` (`ThreeMajority.majority3_consensus_whp`),

both on a minimal *finite uniform* probability layer plus, for 3-majority, a
from-scratch Chernoff bound. Read `docs/DESIGN.md` (representation decisions,
Lean→Rocq dictionary) and `docs/PLAN.md` (milestones, file map, status) before
touching `theories/`. The Lean sources are the specification: statements must
be faithful ports, never weakened.

## Toolchain (never install things ad hoc)

Rocq 9.1.1, MathComp 2.5.0, mathcomp-classical/reals/analysis 1.16.0,
hierarchy-builder 1.10.2, algebra-tactics 1.2.7, zify; opam switch `rocq-9.1.1`
(`eval $(opam env --switch=rocq-9.1.1 --set-switch)`). Rocq stays below 9.2 because
the released coq-lsp/petanque used by rocq-mcp requires `rocq-core < 9.2`. Exact
pins and rationale: `rocq-dynamics.opam`, `docs/study/llm4rocq-tooling.md`.

## Build and gates

```bash
make -j            # builds everything listed in _CoqProject (add new files there, in layer order)
make gate          # check_layers + build + no-Admitted grep + axiom audit (verify.sh)
./verify.sh        # clean rebuild + Print Assumptions of the headline theorems
```

- Layers `prelude < prob < rumor | majority` are enforced by `scripts/check_layers.py`;
  `rumor` and `majority` never import each other.
- Accepted axioms: only `boolp.functional_extensionality_dep`,
  `boolp.propositional_extensionality`, `boolp.constructive_indefinite_description`.
  No `Axiom`/`Parameter`/`Admitted`/`admit` on `main`. Temporary `Admitted` is fine on
  a branch but must be listed in the status table of `docs/PLAN.md`.

## Proving workflow (MCP-first)

The `rocq-mcp` server (user-level MCP, pinned to the `rocq-9.1.1` switch) and the
`rocq` and `mathcomp-skills` plugins are installed at user level.

1. Start each session with `rocq_health`, then
   `rocq_query(preamble="From Dynamics Require Import prelude.", command="Check expR0.")`.
2. Before any Write or `coqc` on a `.v` file: for scratch iteration on a single proof use
   `rocq_start file=<…>.v theorem=<lemma>` and `rocq_step_multi tactics=[...]`, not
   `coqc /tmp/x.v`. Use `coqc`/`make` only for full-project rebuilds, axiom audits and
   final verification.
3. `rocq_query("Search ...")` and `rocqet_search` before writing tactics; check
   `docs/DESIGN.md` §Dictionary first and add every Mathlib→MathComp correspondence
   you discover.
4. `rocq_check` to commit tactics, `rocq_compile_file` as file gate, `make` as project
   gate, `rocq_assumptions` on every new top-level theorem.
5. Statement-first: port a Lean declaration as an `Admitted` skeleton with the Lean
   name and statement in its docstring, get the file compiling
   (`rocq_compile_file mode="vos"`), then prove. Never change a statement to make it
   provable and never silently weaken constants or exponents; if a statement is
   wrong, stop and record the issue in `docs/PLAN.md`.
6. Stage only files you touched; commit often (`checkpoint: ...`); never push, amend,
   or reset (the `rocq` plugin's guardrail hook blocks these anyway).
7. `/mathcomp-review --scope=changed` before `/rocq:checkpoint`.

## Style (MathComp house style; the `mathcomp-skills` plugin is the reference)

- Every file: `From Dynamics Require Import prelude.` first (it brings in
  ssreflect, algebra, boolp, reals, exp, ring/lra/zify and the standard options).
- `Section` + `Variable R : realType` (or `Context {R : realType}`); `Implicit Types`;
  80-character lines; ssreflect tactics; `by`/`exact:` closers.
- Names `mainSymbol_suffixes` in MathComp style (`avg_le`, `expList_add`,
  `avg_exp_le`); lowercase file names. One `(** ... *)` docstring per public
  declaration, quoting the Lean name it ports.
- Finite probability only: probabilities and expectations are `\sum_` bigops divided by
  cardinalities; asymptotics are explicit constants exactly as in the Lean statements.
- `lra`/`nra`/`ring` for real arithmetic (algebra-tactics), `lia`/`nia` for `nat`
  (zify is imported by the prelude).

## Deliverables besides code

Keep `docs/PLAN.md`'s status table current; update `CHANGELOG.md` per milestone; keep
the blueprint (`blueprint/`, once created) in sync with `\rocq{Dynamics.file.lemma}`
tags mirroring the Lean blueprint's `\lean{}` tags.
