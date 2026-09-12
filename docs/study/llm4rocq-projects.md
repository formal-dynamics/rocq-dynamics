# LLM4Rocq formalization repos — layout, build, agent conventions, and a template for us

Scope: the 11 requested directories under `llm4rocq/` (shallow clones, read-only), plus a
short look at the three sibling repos that hold the org's *agent* conventions
(`rocq-skills`, `mathcomp-skills`, `rocq-mcp`) because none of the formalization repos
carries a `CLAUDE.md` of its own. Counts below were produced with `find`/`wc`/`grep`
(`grep -c 'Admitted\|admit\.'`) on 2026-09-10.

## 0. One-table summary

| Repo | What | `.v` files | lines | `Admitted\|admit.` hits | Real hits? | Build | Pins (Rocq / MC / extras) | Agent files | Blueprint |
|---|---|---:|---:|---:|---|---|---|---|---|
| `mathcomp-eulerian` | Stanley EC1 §1.3–1.6: descents, Eulerian numbers, cd-index, FPS sub-library | 49 | 22 475 | 2 | **0** (both are comments in `altsub.v`) | `_CoqProject` + thin Makefile + `.opam` + Dockerfile | 9.1.1 / 2.5.0 / classical 1.16.0, coq-lsp 0.2.5+9.1 | vendored Claude plugin `plugin/rocq/` (+ `.mcp.json`), `pyproject.toml` pinning rocq-mcp/pytanque | rocqblueprint + coqdoc + 105-page "formal companion" PDF, GH Pages |
| `mathcomp-kummer` | Kummer's theorem (p-adic valuation of C(n,k) = carries) | 4 | 613 | 0 | 0 | `_CoqProject` + tiny Makefile | CI: Coq 8.20 + `coq-mathcomp-ssreflect` (imports `all_boot all_order`, i.e. MC ≥ 2.4) | none | rocqblueprint + `blueprint/update_status.py`, GH Pages |
| `mathcomp-qbs` | Quasi-Borel spaces, probability monad, Giry/kernel bridges, Bayesian regression showcase (mathcomp-analysis) | 13 | 9 043 | 0 | 0 | `_CoqProject` + `.opam` (no Makefile checked in) | `coq {>= 9.0 & < 9.2~}`, MC ≥ 2.5.0, **analysis ≥ 1.15 < 1.17**, HB ≥ 1.10, algebra-tactics ≥ 1.2 | none (`.claude/`, `PLAN.md`, `REVIEW.md` gitignored) | rocqblueprint, GH Pages; 71 KB `REPORT.md` |
| `graph-theory-rocq` | Monorepo of 14 opam-style packages stating ~1 700 open graph-theory conjectures as axiom-free `Definition <name>_statement : Prop`, plus a few resolutions | 463 | 59 308 | 73 | mostly *statement stubs / gap-repair files*; `make gate` checks landed milestones are Admitted-free | per-package `_CoqProject`; root Makefile loops `rocq makefile` | base `.opam`: `coq-mathcomp-ssreflect >= 2.5.0`, `coq-graph-theory >= 0.9.7`; dev switch Rocq 9.1.1 | none; huge `meta/` gate scripts | `blueprint/` is a scaffold stub; toolchain-free `corpus-status.yml` CI |
| `digraph-theory` | Directed graphs/tournaments on MathComp + coq-graph-theory; k-ω̄-critical tournament families (k=3,4,5), Cheng–Keevash δ=3 | 34 | 6 958 | 0 | 0 | `_CoqProject` + coq-community Makefile + `rocq-*.opam` & `coq-*.opam` + `meta.yml` | `rocq-core >= 8.19`, MC ≥ 2.5.0, classical ≥ 1.16.0, HB ≥ 1.5.0, coq-graph-theory ≥ 0.9.7; CI image `mathcomp/mathcomp:2.5.0-rocq-prover-9.1` | `CONTRIBUTING.md`, `docs/DESIGN.md`, `.vscode/settings.json`; Python oracles | rocqblueprint + statement-closure audit + PDF, GH Pages |
| `small-prime-gap` | Maynard `M_105 > 4` certified by exact Rayleigh-quotient witness (`vm_compute` over `Z`) | 20 | 9 604 | 1 | **0** (comment in `CharPoly.v`) | `_CoqProject` + `.opam` (build via `coqc` loop) + `verify.sh` | **exact pins** `rocq-core = 9.1.1`, all MC = 2.5.0, HB 1.10.2, elpi 3.3.1, algebra-tactics 1.2.7, bignums | none | rocqblueprint (web+pdf), `AUDITOR_CHECKLIST.md`, `SPEC_TO_PAPER.md` |
| `icones-rocq` | Ehrhard–Geoffroy "Integration in Cones" §2–§9 (SMCC, `!`, Seely) + a PPL layer, on mathcomp-analysis | 77 | 75 482 | 9 | **0** (all comments) | `_CoqProject` + committed generated Makefile + `icones.opam` + `verify.sh` + `tools/check_layers.py` | `rocq-core >= 9.1`, MC `>= 2.5.0 < 2.6`, classical & **analysis `>= 1.16.0 < 1.17`**, HB ≥ 1.10 | none (`.claude/` gitignored); `PLAN.md`, `AUDIT.md`, `docs/PAPER.md` drive agents | blueprint retired 2026-08 → generated "auditor dashboard" (GH Pages) |
| `Putnam2025-Rocq` | 12 Putnam 2025 problems: `problems/*.v` (Admitted statements) + `solutions/*.v` | 24 | 7 697 | 12 | 12 = the 12 *problem statements* by design; all 12 solved | no build system; `verify.py` drives `rocq_verify` from rocq-mcp | opam switch recipe: `rocq-core.9.1.1 rocq-stdlib.9.0.0 rocq-mathcomp-{ssreflect,algebra}.2.5.0 coq-coquelicot.3.4.4 coq-lsp.0.2.5+9.1` | `requirements.txt` pinning rocq-mcp/pytanque commits | none |
| `miniF2F-rocq` | 488 miniF2F statements translated to Rocq (stdlib `Reals`, Coquelicot) | 488 | 5 173 | 305 | benchmark: statements end in `Admitted` | none | none pinned | translator config only | none |
| `CombiBench-rocq` | placeholder README only | 0 | 0 | 0 | – | – | – | – | – |
| `rocq-workbook` | 10 000-problem JSONL dataset (Lean workbook → Rocq), `.v` files not shipped | 0 | 0 | 0 | – | `provenance/materialize.py` | "rocq-analysis" switch: stdlib, Coquelicot, mathcomp, mathcomp-analysis | none | none |

**Most polished exemplars to imitate:** `digraph-theory` (build/CI/opam/docs hygiene, layering,
oracle cross-checks), `mathcomp-eulerian` (blueprint + formal PDF + Docker agent image +
plugin), `mathcomp-qbs` and `icones-rocq` (mathcomp-analysis style, `R : realType`, file header
docs, verify.sh/axiom gates). `mathcomp-kummer` is the minimal starter skeleton.

---

## 1. Per-repo reports

### 1.1 `mathcomp-eulerian`

**What.** Rocq/MathComp formalization of permutation descent statistics, Eulerian numbers,
Stanley Cor. 1.6.5 (`beta_alt_max` in `beta_swap.v`), André reflection (`reflection.v`), a
self-contained formal-power-series sub-library `fps/` (`{fps rat}`, exp/log/composition), and
q-analogues (Carlitz). 49 `.v`, 22 475 lines; README claims 0 Admitted in the active build
chain; grep confirms the 2 hits are prose comments (`altsub.v:819`, `altsub.v:1286`).
Axiom policy is stated per layer: combinatorial core = 0 axioms, `fps/` + `stanley_egf.v`
= the three `mathcomp-classical` axioms. `coqchk` and `Print Assumptions` recipes in README.

**Build & pinning.**
- `_CoqProject` (root-level `.v` files; two namespaces):
  ```
  -R . mathcomp_eulerian
  -R fps mathcomp_fps
  -arg -w -arg -deprecated-library-file
  -arg -w -arg -notation-overridden
  fps/fps.v ... (explicit topological order, heavily commented)
  ```
- `Makefile` = coq-community thin wrapper (`coq_makefile -f _CoqProject -o Makefile.coq`, forwards targets).
- `rocq-mathcomp-eulerian.opam`:
  ```
  depends: [
    "rocq-core" {>= "9.0"}
    "rocq-mathcomp-ssreflect" {>= "2.0.0"}
    "rocq-mathcomp-algebra" {>= "2.0.0"}
    "rocq-mathcomp-classical" {>= "1.0.0"}
  ]
  build: [[ make "-j%{jobs}%" ]]  install: [[ make "install" ]]
  ```
- `Dockerfile` (the *agent image*): `FROM ocaml/opam:debian-12-ocaml-5.2`; installs Node 20 +
  `@anthropic-ai/claude-code`, then
  `opam install -y rocq-core.9.1.1 coq-core.9.1.1 rocq-mathcomp-ssreflect.2.5.0 rocq-mathcomp-fingroup.2.5.0 rocq-mathcomp-algebra.2.5.0 rocq-mathcomp-classical.1.16.0 coq-lsp.0.2.5+9.1`
  (coq-lsp ships `pet-server` for pytanque/rocq-mcp), clones `LLM4Rocq/rocq-mcp` into a venv,
  bakes `/etc/claude/mcp.json` (stdio server `/opt/rocq-mcp/.venv/bin/rocq-mcp`), and
  `ENTRYPOINT claude --mcp-config /etc/claude/mcp.json --dangerously-skip-permissions`.
  Header comment: "Toolchain matches the host snapshot: Rocq 9.1.1, OCaml 5.2.x, mathcomp 2.5.0".
- `pyproject.toml` pins `rocq-mcp` and `pytanque` to git commits via `[tool.uv.sources]`.
- CI `.github/workflows/blueprint.yml`: `coq-community/docker-coq-action@v1` with
  `coq_version: '9.1'`, `ocaml_version: '4.14-flambda'`, `opam install -y coq-mathcomp-ssreflect coq-mathcomp-fingroup coq-mathcomp-algebra coq-mathcomp-classical`,
  then `coq_makefile -f _CoqProject -o CoqMakefile && make -f CoqMakefile -j2 && make -f CoqMakefile html`;
  separate jobs build the rocqblueprint web (`pip install rocqblueprint; cd blueprint/src; rocqblueprint web`)
  and the LaTeX PDF (`docs/formal/extract_catalog.py` then `make`), then combine into `site/`
  (blueprint at `/`, coqdoc at `/doc/`, PDF) and deploy to GitHub Pages.

**Agent-facing conventions.** No `CLAUDE.md`/`AGENTS.md`; `.claude/` is gitignored
("Per-session Claude Code state"), as is `rocq_mcp_cache_*.v`. Instead the repo *vendors a full
Claude Code plugin* at `plugin/rocq/` (identical tree to `rocq-skills/plugins/rocq/`):
- `.claude-plugin/plugin.json` — name `rocq`, "MCP-first, scripts fallback".
- `hooks/hooks.json`: `SessionStart` → `bootstrap.sh` (exports `ROCQ_PLUGIN_ROOT`, `ROCQ_SCRIPTS`, `ROCQ_REFS`, `ROCQ_PYTHON_BIN`); `PreToolUse(Bash)` → `guardrails.sh`, which in any dir containing `_CoqProject`/`CoqMakefile`/`*.v` **blocks** `git push`, `git commit --amend`, `gh pr create` (policy `ask|allow|block`, one-shot bypass `ROCQ_GUARDRAILS_BYPASS=1`) and *always* blocks `git checkout -- / .`, `reset --hard`, `clean -f`, `restore`.
- `commands/*.md`: `/rocq:draft, formalize, autoformalize, prove, autoprove, checkpoint, review, refactor, golf, learn, doctor`. `prove`/`autoprove` share a 6-phase cycle engine (Plan → Work → Checkpoint → Review → Replan → Continue/Stop) with stop rules (`--max-cycles=20`, `--max-total-runtime=120m`, `--max-stuck-cycles=3`), a "header fence" (declaration headers immutable; statement changes only via `formalize`), and staging discipline ("stage only touched files, never `git add -A`").
- `commands/checkpoint.md`: compile each touched file → project build (`make -f CoqMakefile`) → `check_axioms.sh` → `admitted_analyzer.py --format=summary` → commit `checkpoint(rocq): ...`; never push.
- `skills/rocq/SKILL.md` core rules (quoted): "Search before prove", "Build incrementally. Rocq's type checker is your test suite — if it compiles with no `Admitted` and standard axioms only, the proof is sound", "Use 80-character line width", "Never change statements or add axioms without explicit permission", MCP tools normative (`rocq_start/check/step_multi/compile/query/verify`), quality gate = compile + zero Admitted + only standard axioms (`classic`, `functional_extensionality`, `propositional_extensionality`, `proof_irrelevance`) + `rocq_verify`. Automation cascade: `reflexivity → auto → trivial → ring → lia → lra → nia → nra → tauto → firstorder → intuition → eauto → decide`.
- `agents/`: `admitted-filler-deep` (model: opus, allowed MCP tools listed), `proof-repair`, `proof-golfer`, `axiom-eliminator`.
- `lib/scripts/`: `admitted_analyzer.py`, `check_axioms.sh` (greps `Axiom|Parameter|Conjecture`), `smart_search.sh`, `find_golfable.py`, `find_usages.sh`, `parse_rocq_errors.py`.
- `plugin/rocq/.mcp.json`: `{"rocq-mcp": {"type":"stdio","command":"uv","args":["run","rocq-mcp"],"env":{"ROCQ_COQC_TIMEOUT":"120","ROCQ_VERIFY_TIMEOUT":"240",...}}}`.
- Planning docs the agent works from: `docs/internal/*PLAN*.md`, `docs/plans/*_PLAN.md` (one plan per file family, e.g. `FPS_PLAN.md`), `NEXT_SESSION.md`, `AXIOMS_TODO.md`, and paper excerpts in `refs/`.

**Style.** `From mathcomp Require Import all_ssreflect fingroup perm binomial ssrint ssralg.`
then `From mathcomp_eulerian Require Import ...`; `Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.`;
banner comments `(* ===== *)` per topic; **every** lemma has a `(** ... *)` coqdoc docstring
(928 `(**` lines) referencing Stanley ("Stanley EC1, S1.4"); 76 `Section`s; names
snake_case, conclusion-based (`eulerian_row_sum_fact`, `des_rev_perm`). Numbers: `nat`, `int`,
`rat`, `{fps rat}`, `{poly int}`; no reals. Probability: none. Big sums everywhere
(`\sum_(k < n.+1) eulerian n k`, `partition_big`, `eq_bigr`).

**Blueprint / paper-to-code.** Four artifacts: (1) rocqblueprint site (`blueprint/src/{web,print,content}.tex`, `macros/`, `plastex.cfg` with `plugins=plastexdepgraph rocqblueprint`), convention
`\begin{theorem}[Stanley Prop 1.6.4]\label{..}\uses{..}\rocq{mathcomp_eulerian.perm_seq_bridge.omega_proper_beta_lt}\rocqok`;
(2) `docs/formal/eulerian_formal.pdf` — Stanley-style PDF with verbatim Rocq listings and
`\rocqsource{file}{line}` GitHub links, Appendix = auto-generated lemma catalog
(`docs/formal/extract_catalog.py` parses `_CoqProject` + docstrings); (3) `PROOF_STATEMENTS.md`,
`FORMAL_VS_STANLEY.md`, `docs/DEFINITIONS_AUDIT.md` (formal-vs-informal definition audit with
file:line); (4) `docs/READING_GUIDE.md`.

### 1.2 `mathcomp-kummer`

**What.** Kummer's theorem and digit-sum reformulation on top of MathComp's `logn_fact`
(Legendre). 4 files, 613 lines, 0 Admitted, all lines ≤ 80 chars.

**Build.** `_CoqProject`: `-R theories MathCompKummer`, `-arg -w -arg -notation-overridden`,
4 files. `Makefile` (minimal): `coq_makefile -f _CoqProject -o CoqMakefile` then `make -f CoqMakefile`.
No `.opam`. CI `blueprint.yml`: docker-coq-action `coq_version: '8.20'`, `opam install coq-mathcomp-ssreflect -y`;
build + `make html`; rocqblueprint job; combine + deploy Pages (coqdoc under `/doc/`). Note the
sources import `all_boot all_order` (MathComp ≥ 2.4 module names), so CI at "8.20 + latest
ssreflect" works only because `coq-mathcomp-ssreflect` resolves to a 2.4+/2.5 release.

**Agent files.** None. `blueprint_plan.md` (17 KB) is the agent's plan and even contains the
"initialization steps" shell recipe (`rocqblueprint new`, `_CoqProject` heredoc).
`MEMO_mathcomp_integration.md` records what already exists upstream (table of MathComp lemmas
used) and upstreaming options — a good "search before prove" artifact.

**Style.** `(** * Title *)` file header + `(** ** Section *)`; `From mathcomp Require Import all_boot all_order.`;
short ssreflect proofs (`by rewrite ...`), `have` chains; no `Section`s; naming `logn_bin_eq0`,
`kummer_digit_sum`. Numbers: `nat` only.

**Blueprint.** rocqblueprint (`blueprint/src/ch_*.tex`, one chapter per `.v`), plus
`blueprint/update_status.py` that scans `.v` files to sync `\rocqok` status.

### 1.3 `mathcomp-qbs`

**What.** Quasi-Borel spaces (Heunen–Kammar–Staton–Yang) in mathcomp-analysis: cartesian
closure, L⊣R adjunction, probability monad with setoid monad laws, integration, expectation/
variance, independence, Giry and s-finite kernel bridges, `R ≅ R×R`, Bayesian linear
regression showcase. README: "Claude wrote all 9,043 lines (414 proofs, 0 Admitted) with
guidance from a human collaborator". 13 files, 9 043 lines, 0 Admitted.

**Build & pinning.** `_CoqProject`: `-Q theories QBS` + 13 files. No Makefile committed
(README: `coq_makefile -f _CoqProject -o Makefile; make -j4`; `Makefile` gitignored).
`coq-qbs.opam`:
```
depends: [
  "coq" {>= "9.0" & < "9.2~"}
  "coq-mathcomp-ssreflect" {>= "2.5.0"}
  "coq-mathcomp-algebra" {>= "2.5.0"}
  "coq-mathcomp-analysis" {>= "1.15.0" & < "1.17~"}
  "coq-hierarchy-builder" {>= "1.10.0"}
  "coq-mathcomp-algebra-tactics" {>= "1.2.0"}
]
build: [["coq_makefile" "-f" "_CoqProject" "-o" "Makefile"] [make "-j%{jobs}%"]]
```
CI: docker-coq-action with `opam_file: coq-qbs.opam`, `coq_version: '9.0.1'`, `ocaml_version: 'default'`
(the action does `opam pin --deps-only` from the opam file), coqdoc via `rocq makefile ... Makefile.doc; make -f Makefile.doc html`,
rocqblueprint web, deploy.

**Agent files.** None; `.gitignore` excludes `.claude/`, `PLAN.md`, `REVIEW.md`, `MATHCOMP_SPECIALIST.md`,
`TODO_FIXES.md`, `.tmp*`, `rocq_mcp_cache_*.v` — i.e. the agent's working notes are kept local.

**Style (the mathcomp-analysis house style).** Files open with the analysis copyright line,
`From HB Require Import structures.`, `From mathcomp Require Import all_boot all_algebra reals classical_sets boolp ereal measurable_structure ... probability ...`,
then an `(**md*****)` header block listing every definition as `name == meaning` (exactly like
`math-comp/analysis` files), `Import GRing.Theory Num.Def Num.Theory.`, `Local Open Scope classical_set_scope.`,
`Section ... Variable R : realType. Local Notation mR := (measurableTypeR R). Implicit Types (X Y Z : qbsType R).`
HB structures via `HB.mixin`/`HB.instance` (38 `HB.` uses), 77 Sections, 2 lines > 80 chars.
**Probability material:** `theories/probability_qbs.v` — `qbs_prob` (random element + `probability mR R`),
`qbs_prob_equiv`, `qbs_return`, `qbs_bind`, `qbs_bindA`, `qbs_integral`, `qbs_expect`,
`qbs_prob_event`, `qbs_variance`, `qbs_integrable*`, `qbs_integralD/B/Zl`; `REPORT.md` §2.16
"Integrability and Probability Inequalities", §2.20 "Independence", §2.21 "Variance of
Independent Sums"; `pair_qbs_measure.v` — `qbs_pair_integral_factorization`,
`qbs_integral_indep_factorization` (E[fg]=E[f]E[g]); `measure_as_qbs_measure.v` —
`qbs_expect_normal/bernoulli/uniform`. All measure-theoretic (Lebesgue integral, `\bar R`),
imports mathcomp-analysis `probability` and `hoelder`. No Chernoff/Hoeffding.

**Blueprint.** rocqblueprint with `\rocq{QBS.file.name}`, `\rocqok`, `\uses`; 71 KB
`REPORT.md` (formalization report with lemma-by-lemma TOC and "Limitations" section).

### 1.4 `graph-theory-rocq`

**What.** Monorepo (math-comp model: one repo, many packages `base/`, `chromatic-theory/`, …,
14 areas) whose main deliverable is *statements*: each open conjecture is an axiom-free
`Definition <name>_statement : Prop` with faithfulness audits; ~1 700 rows tracked; plus a few
checked resolutions and "gap repairs". 463 `.v`, 59 308 lines. 73 `Admitted/admit.` hits
(concentrated in `digraph-theory/` subtree = 21 and area packages); the acceptance gate
`meta/check_milestone.py` requires *landed* milestones to have "no top-level
Axiom/Parameter/Admitted/Conjecture/Hypothesis" and `Print Assumptions` closed.

**Build & pinning.** Root `Makefile`: `PACKAGES := base chromatic-theory ...`; per package
`cd $@ && rocq makefile -f _CoqProject -o Makefile.coq && make -f Makefile.coq`; dependency
edges `<pkg>: base`; targets `gate`, `audit` (toolchain-free), `mutation`, `probe`,
`resolutions`, `gap-repairs`. Cross-package loadpath via `_CoqProject` lines
`-R theories Chromatic` + `-Q ../base/theories GTBase`. `base/coq-graph-theory-base.opam`:
`depends: [ "coq-mathcomp-ssreflect" {>= "2.5.0"} "coq-graph-theory" {>= "0.9.7"} ]`,
`build: [["rocq" "makefile" "-f" "_CoqProject" "-o" "Makefile.coq"] [make "-f" "Makefile.coq" "-j" "%{jobs}%"]]`.
`meta/rocq_toolchain.py` selects the opam switch (`ROCQ_OPAM_SWITCH`, default `digraph` =
Rocq 9.1.1 + MC 2.5.0). CI `corpus-status.yml` runs only `make audit` (Python, no Rocq).

**Agent files.** None. The agent operating manual is `meta/`: `OPG_FULL_FORMALIZATION_PLAN.md`,
`V2_FULL_CORPUS_PLAN.md`, `CORPUS_STATUS.md`, `FAITHFULNESS_CHECKS.md`, per-wave
`X*_faithfulness_audit.md`, JSON manifests, `check_milestone.py`, `vacuity_probe.py`
(tries to prove each statement *and its negation* with an automation ladder — a settleable
"open conjecture" is flagged as mis-encoded), `faithfulness_mutation.py`.

**Style.** `From mathcomp Require Import all_boot.` (125×), `From HB Require Import structures.`,
`From GTBase Require Export base.`; per-file `(** * Ns.conjectures.X3 -- ... *)` header; local
vocabulary prefixed by wave id (`x3_hole`, `x3_stable_set`). **Asymptotics without reals:**
`base/theories/asymptotics.v` defines `eventually`, `big_O_nat`, `little_o_nat`,
`subpolynomial_nat`, `near_linear_lower_nat` on `nat -> nat` using cross-multiplied rational
epsilons ("no limits, no reals, no axioms"). **Finite probability as exact rationals:**
`extremal-graph-theory/theories/conjectures/D2pr.v` header: "FINITE PROBABILITY IS EXACT …
`E[X] = (\sum_outcomes X)/N`, `P(A) = #|A|/N`", `Definition Echi (G:sgraph) : rat`, whp/Θ
rendered as eventual ε–N over `nat`. Directly relevant to our project as the *cheap* option.

**Blueprint.** `blueprint/README.md` = scaffold stub ("Status: scaffold"); the audit/site
tooling is in `meta/` and in the absorbed `digraph-theory/`.

### 1.5 `digraph-theory`

**What.** Standalone version of the directed-graph library (later subtree-merged into
`graph-theory-rocq`): HB hierarchy `DiGraph → Oriented → Tournament`, ω̄ via `arg min` over
`{perm T}` and coq-graph-theory's `omega`, substitution/Cayley/circulant constructions,
and the headline `conjecture_5_10_at_345` (`applications/unified.v`). 34 files, 6 958 lines,
0 Admitted, everything `Print Assumptions`-clean (CI-audited).

**Build & pinning (cleanest in the org).**
- `_CoqProject`: `-R theories Digraph`, `-arg -w -arg -notation-overridden,-ambiguous-paths`, files grouped by layer comments (`# --- foundations ---`, `# --- core ---`, …).
- `Makefile`: coq-community thin wrapper ("Works with `coq_makefile` / `rocq makefile`"), `Makefile.coq: Makefile _CoqProject`, `clean::`, catch-all `%: invoke-coqmakefile`.
- Two opam files (`rocq-digraph-theory.opam` canonical, `coq-digraph-theory.opam` compat):
  ```
  depends: [
    "rocq-core"                 { >= "8.19"  }
    "rocq-mathcomp-ssreflect"   { >= "2.5.0" }
    "rocq-mathcomp-algebra"     { >= "2.5.0" }
    "rocq-mathcomp-fingroup"    { >= "2.5.0" }
    "rocq-mathcomp-classical"   { >= "1.16.0" }
    "rocq-hierarchy-builder"    { >= "1.5.0" }
    "coq-graph-theory"          { >= "0.9.7" }
  ]
  tags: [ "category:Mathematics/Combinatorics and Graph Theory/Graph Theory" ... "logpath:Digraph" ]
  ```
- `meta.yml` for the rocq-community template generator (kept in sync by hand).
- CI `ci.yml`: `coq-community/docker-coq-action@v1` with `custom_image: 'mathcomp/mathcomp:2.5.0-rocq-prover-9.1'`
  ("Matches the local dev switch `digraph` (Rocq 9.1.1 + MathComp 2.5.0); tag existence verified on Docker Hub"),
  `install: opam install -y rocq-mathcomp-classical coq-graph-theory`, `script: make -j2`, chown workaround.
- CI `blueprint.yml`: same image; after `make -j2` runs `scripts/statement_closure.py --check`,
  regenerates quotes/panels/blueprint/catalog and **fails on `git diff --exit-code`** (committed
  artifacts must equal regenerated ones), then `scripts/axiom_audit.py` (compiles a probe file
  of `Print Assumptions` for all 33 catalog results, asserts N× "Closed under the global context"),
  coqdoc; separate rocqblueprint + PDF jobs; deploy to Pages.
- README install recipe: `opam switch create . --packages=rocq-prover.9.1.1; opam repo add rocq-released https://rocq-prover.org/opam/released; opam install rocq-mathcomp-ssreflect rocq-mathcomp-algebra rocq-mathcomp-fingroup rocq-mathcomp-classical rocq-hierarchy-builder coq-graph-theory`.
  Dev switch recorded: "Rocq 9.1.1 + MathComp 2.5.0 + mathcomp-classical 1.16.0 + HB 1.10.2 + coq-graph-theory 0.9.7".

**Agent-facing conventions.** No CLAUDE.md, but `CONTRIBUTING.md` is effectively one:
"Read `docs/DESIGN.md` first"; "Layering is strict. A module may only import from the same
or lower layers (`foundations < core < invariants < constructions < applications`)";
"`coq-graph-theory` is imported in exactly one file, `foundations/interop_graph_theory.v`";
"Reuse over reinvention"; "Lowercase file names, MathComp/SSReflect proof style"; "Each new
public definition gets a one-line doc comment; each milestone updates `CHANGELOG.md`"; "Keep
`make` green; add a smoke/regression check when a definition is meant to compute (cross-check
against the Python oracle)". `docs/DESIGN.md` (v1.2) records the ecosystem survey table
("Need / Already exists? / Verdict: Reuse|Build"), design principles, decisions D1–D20,
milestones M0–M21. `scripts/*.py` = exact Python oracles + pytest suites
(`uv run --with pytest ... pytest scripts/`). `.vscode/settings.json` hides `*.vo` etc.
`.gitignore` covers `_opam` (switch link), `rocq_mcp_cache_*.v`.

**Style.** `theories/foundations/prelude.v` is the shared prelude ("Every other file should
`From Digraph Require Import prelude.` first"): `From mathcomp Require Import all_boot. From mathcomp Require Import boolp classical_sets.`,
the three `Set Implicit Arguments...` lines, `Local Open Scope classical_set_scope.`, smoke
lemmas (`prelude_classical`, `prelude_set`, `prelude_ssr`) "so a broken toolchain fails fast at
`make` time", and generic counting lemmas (`card_classes`). Every file: `(** * Digraph.omegabar — title` + paragraph
listing "Main results here: - [omegabar_min] …" + oracle cross-check note `*)`. `Notation "ω̄( T )"`
with unicode; 49 Sections, 32 `HB.`, 55 lines > 80. Numbers: `nat`, `'Z_n`; no reals, no probability.

**Blueprint.** Result-first site: `scripts/statement_closure.py` computes from `.glob` files
the *statement* dependency closure of each catalog result and gates that every constant maps
to a documented "def-block" (`docs/web/defblocks.json`); `extract_quotes.py` extracts verbatim
statements at build time ("never hand-copied"); `gen_blueprint.py` emits plasTeX chapters with
`\uses` edges from `closure.json`; `docs/formal/digraph_formal.pdf`. `docs/PLAN_WEB.md` explains
the 6-part page template (informal statement, verbatim formal statement + GitHub link,
"Decoded" line, statement closure with faithfulness notes, trust box, dep-graph neighbourhood;
"Anti-goal: no proofs").

### 1.6 `small-prime-gap`

**What.** Kernel-checked replacement for the Mathematica step in Maynard's *Small gaps
between primes*: `maynard_M105_certified_rayleigh` in `theories/S1/CertRayleigh.v`
(42×42 rational matrices from FLINT, exact Rayleigh-quotient witness, `vm_compute` over `Z`),
"Closed under the global context". 20 files, 9 604 lines (5 705 are the autogenerated
`Witness.v`), 0 real Admitted (1 comment hit).

**Build & pinning.** `_CoqProject`: `-Q theories/S1 PrimeGapS1` + 20 files (no Makefile; README
uses `coq_makefile -f _CoqProject -o Makefile; make -j8`, `Makefile` gitignored). `coq-prime-gap.opam`
is the only repo with **exact** pins:
```
# Pinned to the exact versions used to verify the headline theorem.
# Last full-rebuild validation: Rocq 9.1.1 + MathComp 2.5.0, ~29 min make -j.
"rocq-core" {= "9.1.1"}
"rocq-mathcomp-ssreflect" {= "2.5.0"} "rocq-mathcomp-boot" {= "2.5.0"} "rocq-mathcomp-order" {= "2.5.0"}
"rocq-mathcomp-fingroup" {= "2.5.0"} "rocq-mathcomp-algebra" {= "2.5.0"} "rocq-mathcomp-solvable" {= "2.5.0"}
"rocq-mathcomp-field" {= "2.5.0"}
"coq-mathcomp-real-closed" {= "2.0.3"} "coq-mathcomp-multinomials" {= "2.4.0"}
"coq-mathcomp-algebra-tactics" {= "1.2.7"} "coq-mathcomp-bigenough" {= "1.0.4"}
"coq-mathcomp-finmap" {= "2.2.2"} "coq-mathcomp-zify" {= "1.6.0+2.3+8.18"}
"rocq-bignums" {= "9.0.0+rocq9.1"} "rocq-hierarchy-builder" {= "1.10.2"} "rocq-elpi" {= "3.3.1"}
```
`verify.sh`: `make clean && make -j` then `coqtop -Q theories/S1 PrimeGapS1 -l theories/S1/Cert.v -batch -e 'Print Assumptions maynard_M105_certified.'`.
CI `blueprint.yml`: docker-coq-action `opam_file: coq-prime-gap.opam`, `coq_version: '9.1.1'`; the
full build is too slow for a runner, so coqdoc is "best effort" (`make -f Makefile.doc html || true`);
rocqblueprint web + pdf; deploy only on push to main. `requirements.txt`: `python-flint==0.8.0`.

**Agent files.** None (`.claude/`, `AUDIT.md`, `audit_*.md`, `survey_*.md` gitignored). Deliverable
docs: `REPORT.md`, `SPEC_TO_PAPER.md` (line-level map `MaynardSpec.v` ↔ arXiv §8),
`AUDITOR_CHECKLIST.md` (claim → Maynard ref → Rocq lemma table; "An auditor who trusts the
kernel reads only the composed headline"), `notebook_reconstructed.md`. README carries the
honest "WARNING: … the code in this repository has been produced by a machine".

**Style.** Mixed: `From mathcomp Require Import all_ssreflect all_algebra.` for the `rat`
spec, `From Stdlib Require Import ZArith List Lia.` for the computational refinement,
`From Bignums Require Import BigZ.`; autogenerated data files carry a provenance header
("AUTOGENERATED by python/build_quad_witness.py — do not edit", generator parameters, slack).
Numbers: `rat` (paper-form spec) refined to `Z` pairs; no reals; no probability.

### 1.7 `icones-rocq`

**What.** Ehrhard–Geoffroy *Integration in Cones* §2–§9 fully formalized (cones, measurable/
integrable cones, Pettis integral, Fubini, SMCC via a mechanized SAFT, stable maps CCC with
fixpoints, `!` comonad, Seely category, `FMeas` coalgebra) plus a PPL layer (rejection
sampling = conditioning). 77 files, 75 482 lines; 0 real Admitted (9 comment hits), only the
three `boolp` axioms (`AUDIT.md`: adversarial audit, "0 BLOCKER, 0 major").

**Build & pinning.** `_CoqProject`: `-Q theories Icones`, seven `-arg -w -arg -<warning>`
lines (incl. `-deprecated-since-mathcomp-analysis-1.9.0`, `-deprecated-since-mathcomp-2.5.0`),
and a documented **import-layer table** ("A file may only Require files in a strictly lower
layer, or in its own layer") enforced by `tools/check_layers.py` (ranks
`prelude < cones < mcones < icones < homs|stable < kernels|exp < cbv < programs`). The
`coq_makefile`-generated `Makefile` (Rocq 9.1.1 header) is committed. `icones.opam`
(`name: "rocq-icones"`):
```
"rocq-core" { >= "9.1" }
"rocq-mathcomp-ssreflect" { >= "2.5.0" & < "2.6" }
"rocq-mathcomp-algebra" { >= "2.5.0" & < "2.6" }
"rocq-mathcomp-classical" { >= "1.16.0" & < "1.17" }
"rocq-mathcomp-analysis" { >= "1.16.0" & < "1.17" }
"rocq-hierarchy-builder" { >= "1.10.0" }
```
Two workflows: **`build.yml` (gating)** — `python3 tools/check_layers.py` first (cheap), then
docker-coq-action `opam_file: icones.opam`, `coq_version: '9.1.1'`, `make -j2`, `./verify.sh`
(clean rebuild + `Print Assumptions` of 8 headline theorems piped to `rocq repl -q -Q theories Icones`,
expecting only `boolp.functional_extensionality_dep`, `boolp.propositional_extensionality`,
`boolp.constructive_indefinite_description`), and uploads the `.glob` tarball as an artifact;
**`blueprint.yml` (docs, non-blocking)** — builds an "auditor dashboard" from `docs/PAPER.md`,
`docs/PPL.md`, `docs/EXAMPLES.md` (`tools/build_auditor.py`), reusing the `.glob` artifact
for real dependency edges, with elaborate fallback/provenance logic.

**Agent files.** None (`.claude/` gitignored: "Claude Code local lock files"). `PLAN.md` (67 KB)
is the formalization plan with LoC estimates per paper section and MVP/stretch tiers;
`AUDIT.md` is a red-team audit; `docs/AUDITOR_FORMAT.md` is the parser contract for the
paper-to-Rocq mapping markdown.

**Style.** `From mathcomp Require Import all_ssreflect ssralg ssrnum. From mathcomp.classical Require Import boolp. From mathcomp.reals Require Import reals. From mathcomp.algebra Require Import interval_inference. From HB Require Import structures.`
then fully-qualified `Require Import Icones.cones.precone.`; long `(** * Cones — Paper §2.1 … Design notes … *)`
headers citing paper page numbers; `Import Order.TTheory GRing.Theory Num.Theory. Local Open Scope ring_scope.`;
`R : realType` throughout (76 files); 627 Sections, 126 `HB.`, 672 Notations, 3 604 coqdoc
lines, 541 lines > 80. Probability: measure-theoretic (`theories/programs/distributions.v`,
`bool_cone.v`, `fmeas.v`), no finite-distribution/Chernoff material.

### 1.8 `Putnam2025-Rocq`

**What.** 12 Putnam 2025 problems; `problems/putnam_2025_*.v` are statements ending in
`Proof. Admitted.`, `solutions/proof_*.v` the proofs; all 12 verified (paper arXiv:2603.20405,
"Claude Code + Opus 4.6 + Rocq-MCP"). 24 files, 7 697 lines; the 12 Admitted are by design.

**Build.** None; `verify.py` calls `rocq_mcp.server.rocq_verify(proof, problem_name, problem_statement, workspace)`
per problem and prints the README status table with axioms. Setup recipe in README:
`opam switch create putnam25 ocaml-base-compiler.5.2.1`, `opam repo add rocq-released https://rocq-prover.org/opam/released`,
`opam pin add -n rocq-mathcomp-eulerian git+https://github.com/LLM4Rocq/mathcomp-eulerian.git#v0.1.0`,
`opam install rocq-core.9.1.1 rocq-stdlib.9.0.0 rocq-mathcomp-ssreflect.2.5.0 rocq-mathcomp-algebra.2.5.0 coq-coquelicot.3.4.4 coq-lsp.0.2.5+9.1 rocq-mathcomp-eulerian`
("`coq-lsp` … ships the `pet` binary that `verify.py` drives"). `requirements.txt` pins
`rocq-mcp @ git+...@45ebc9d`, `pytanque @ git+...@060e69d`, `tqdm`.

**Style.** Stdlib style (`From Stdlib Require Import Reals Lra.`, `From Coquelicot Require Import Coquelicot.`,
`Z`, `Q`), plain `intros/destruct/lia` proofs; A5 reuses `mathcomp-eulerian`. Reals = stdlib
`Reals` (axioms `ClassicalDedekindReals.*` appear in the table).

### 1.9 `miniF2F-rocq`

488 statement files (`valid/`, `test/`), 5 173 lines, 305 `Admitted` (benchmark statements).
`Require Import Reals.` (248×), `Coquelicot` (38×), `ZArith`, `Arith`. No build system; a
Hydra-configured translator (`translator/conf/config.yaml`, petanque at `127.0.0.1:8765`).
`audit.txt` records the human audit (115 unchanged, 26 syntax, 6 reformulated, 3 wrong).
Not a template source, but shows the org's benchmark convention: statement file =
imports + `Theorem name : ... Proof. Admitted.`

### 1.10 `CombiBench-rocq`, `rocq-workbook`

`CombiBench-rocq`: README stub only. `rocq-workbook`: 36 MB JSONL of 10 000 Lean-workbook
problems with type-checked Rocq statements (`rocq_imports/rocq_preamble/rocq_statement/rocq_proof`
fields), 2 478 proved; libraries "stdlib 8,936 · mathcomp 694 · coquelicot 321 ·
mathcomp-analysis 49"; `docs/TRANSLATION_GUIDE.md` (Lean→Rocq conventions),
`AUDIT_ERROR_TAXONOMY.md`. No `.v` shipped.

---

## 2. Cross-cutting observations

### 2.1 Versions actually pinned (as of mid-2026)

| Component | Evidence | Value |
|---|---|---|
| Rocq | eulerian Dockerfile, prime-gap opam (`=`), icones CI, digraph CI image, Putnam recipe, mathcomp-skills "Tested" | **9.1.1** (opam `rocq-core.9.1.1`, `rocq-prover.9.1.1`) |
| OCaml | eulerian Dockerfile `ocaml/opam:debian-12-ocaml-5.2`; Putnam `ocaml-base-compiler.5.2.1`; eulerian CI `4.14-flambda` | 5.2.x (4.14 also fine) |
| MathComp | all repos | **2.5.0** (`rocq-mathcomp-{boot,order,ssreflect,fingroup,algebra,solvable,field}`) |
| mathcomp-classical | digraph, eulerian Dockerfile, icones | **1.16.0** |
| mathcomp-analysis | icones `>= 1.16 < 1.17`, qbs `>= 1.15 < 1.17`, mathcomp-skills | **1.16.0** (`rocq-mathcomp-analysis`) |
| Hierarchy Builder | prime-gap, digraph DESIGN, mathcomp-skills | **1.10.2** (`rocq-hierarchy-builder`), elpi 3.3.1 |
| algebra-tactics | prime-gap, mathcomp-skills | **1.2.7** (`coq-mathcomp-algebra-tactics`) |
| zify / finmap / bigenough | prime-gap | 1.6.0+2.3+8.18 / 2.2.2 / 1.0.4 |
| coq-lsp (provides `pet`/`pet-server` for pytanque & rocq-mcp) | eulerian Dockerfile, Putnam | **0.2.5+9.1** |
| coq-graph-theory | digraph | 0.9.7 |
| Docker image used in CI | digraph `ci.yml` | `mathcomp/mathcomp:2.5.0-rocq-prover-9.1` (then `opam install rocq-mathcomp-classical ...`) |
| rocq-mcp / pytanque | eulerian `pyproject.toml`, Putnam `requirements.txt` | git-commit pinned via uv sources |
| infotheo | – | **used by no repo** |

Package naming: newer repos use `rocq-*` opam names (`rocq-core`, `rocq-mathcomp-ssreflect`,
`rocq-mathcomp-classical`, `rocq-hierarchy-builder`); `coq-graph-theory`, `coq-mathcomp-algebra-tactics`,
`coq-lsp` keep `coq-` names. `digraph-theory` ships both a `rocq-*.opam` and a `coq-*.opam` compat.

### 2.2 Build-system consensus

Every formalization repo uses **`_CoqProject` + `coq_makefile`/`rocq makefile`**; none uses dune,
nix, or flakes. Common `_CoqProject` shape: one `-R theories <Ns>` (or `-Q`), warning flags via
`-arg -w -arg -notation-overridden[,...]`, and an *explicit, commented, dependency-ordered file
list* (never globs). The Makefile is the coq-community thin wrapper (digraph-theory's is the
reference copy; eulerian's is the same). Icones commits the generated Makefile instead.
Every repo gitignores `*.vo *.vok *.vos *.glob *.aux .*.aux Makefile.coq Makefile.coq.conf .Makefile.coq.d .lia.cache .nia.cache rocq_mcp_cache_*.v .claude/ .venv/`.

### 2.3 CI consensus

`coq-community/docker-coq-action@v1`, two flavours: (a) `opam_file: <pkg>.opam` +
`coq_version: '9.1.1'` + `ocaml_version: 'default'` (qbs, prime-gap, icones); (b)
`custom_image: 'mathcomp/mathcomp:2.5.0-rocq-prover-9.1'` + `install: opam install -y <extra deps>`
(digraph). Always the `sudo chown -R 1000:1000 .` before_script and `sudo chown -R 1001:116 .`
revert. Best practice (icones, digraph): a **gating** `build.yml` (build + `verify.sh`/axiom audit)
separate from a **non-blocking** docs/Pages workflow; the docs workflow regenerates artifacts and
fails on `git diff --exit-code` (digraph).

### 2.4 Verification gates the org relies on (all reusable by us)

1. `grep`-level: no `Admitted|admit.|Axiom|Parameter|Conjecture|Hypothesis` at top level outside comments (`check_milestone.py` strips nested comments first).
2. `Print Assumptions <headline>.` must print "Closed under the global context" or only the three `boolp` axioms (`verify.sh` in icones/prime-gap; `axiom_audit.py` compiles a probe `.v` and counts occurrences).
3. Statement faithfulness: verbatim statements extracted from source at build time (`extract_quotes.py`), definition closure documented (`statement_closure.py`), definition-by-definition audit (`DEFINITIONS_AUDIT.md`, `SPEC_TO_PAPER.md`, `AUDITOR_CHECKLIST.md`).
4. Independent oracle: Python brute-force checkers with pytest (`digraph-theory/scripts/`), FLINT (`small-prime-gap/python/`).
5. Vacuity probe: try to prove the statement *and* its negation by automation; both must fail (`graph-theory-rocq/meta/vacuity_probe.py`).
6. Layering: `tools/check_layers.py` (icones), CONTRIBUTING rule + single interop file (digraph).

### 2.5 How the agents are actually instructed

- **No repo-level CLAUDE.md/AGENTS.md/.claude anywhere** (deep `find` confirmed). `.claude/` is gitignored in eulerian, qbs, prime-gap, icones.
- The instructions live in *user-level* plugins: `rocq-skills` (the `/rocq:*` cycle engine, guardrails, `check_axioms.sh`, `admitted_analyzer.py`) and `mathcomp-skills` (`~/.claude/skills/mathcomp-skills`, auto-attaches on `**/*.v`; 3 270-line `reference.md` = MathComp/analysis CONTRIBUTING rules §1–§37; `templates.md`, `phrasebook.md`, `errors.md`, `proof-development.md`; PostToolUse hook `hooks/run-audit.sh` runs `scripts/audit-quick.sh` on each edited `.v` and returns advisory `additionalContext`; `/mathcomp-review` command + `mathcomp-style-auditor` agent). `mathcomp-eulerian` vendors the rocq plugin under `plugin/rocq/` so it travels with the repo/Docker image.
- MCP: `rocq-mcp` (13 tools: `rocq_compile`, `rocq_compile_file`, `rocq_verify`, `rocq_query`, `rocq_assumptions`, `rocq_start`, `rocq_check`, `rocq_step_multi`, `rocq_toc`, `rocq_notations`, `rocq_diag`, `rocq_health`, `rocq_switch`) registered via `.mcp.json` / `claude mcp add --scope project rocq-mcp -- uvx rocq-mcp`, or baked into the Docker image (`--mcp-config /etc/claude/mcp.json`). It parses `_CoqProject` for load paths and needs `pet` from `coq-lsp`.
- Repo-level *plans* are the real steering documents: `PLAN.md` / `docs/plans/*_PLAN.md` / `docs/DESIGN.md` / `blueprint_plan.md` with milestones, decisions ("D7 resolved"), ecosystem-survey tables ("Reuse / Build"), and `NEXT_SESSION.md`; plus honesty artifacts written by the agent for humans (`REPORT.md`, `AUDIT.md`, `CHANGELOG.md`).
- Style rules quoted by the plugins/CONTRIBUTING: 80-char lines; MathComp naming `mainSymbol_suffixes` (`eulerian_row_sum_fact`, `omegabar_sub`); `by`/`exact` closers; one-line doc comment per public definition; lowercase file names; `Search` before writing tactics; never change statements/headers, never add axioms without permission; stage only touched files; checkpoint commits, no push.

### 2.6 Reals and probability in the org

- No Chernoff/Hoeffding anywhere (grep `chernoff|hoeffding` = 0 hits).
- Reals: mathcomp-analysis `R : realType` in qbs/icones (`From mathcomp Require Import ... reals`, `Import GRing.Theory Num.Def Num.Theory`, `Local Open Scope ring_scope`); exact `rat` in eulerian/prime-gap/graph-theory-rocq; stdlib `Reals`+Coquelicot only in the benchmark repos.
- Finite probability: `graph-theory-rocq/extremal-graph-theory/theories/conjectures/D2pr.v` (exact `rat` counting quotients, whp as eventual ε–N over `nat`), `GTBase.asymptotics` (nat-valued O/o/Θ). Measure-theoretic expectation/variance/independence in `mathcomp-qbs` (`qbs_expect`, `qbs_variance`, `qbs_integral_indep_factorization`).
- mathcomp-analysis 1.16 itself ships `probability.v` (imported by qbs) with `probability`, `expectation`, `variance`, and Markov/Chebyshev-type inequalities and Bernoulli/binomial distributions — worth a `rocq_query("Search ... in probability")` before writing our own; but all of it is measure-based (`\bar R`, Lebesgue integral).

---

## 3. RECOMMENDED PROJECT TEMPLATE FOR US

Goal: port a Lean 4 + Mathlib development (rumor spreading on K_n in O(log n) rounds w.h.p.;
3-majority consensus w.h.p.; minimal finite-probability layer with a self-contained Chernoff
bound) to Rocq + MathComp, with Claude Code doing most proving, on a machine with Docker/
Podman + uv but no opam.

### 3.1 Design decisions (with the evidence behind them)

1. **Toolchain = the org's mid-2026 consensus:** Rocq 9.1.1, MathComp 2.5.0, mathcomp-classical 1.16.0, mathcomp-analysis 1.16.0, HB 1.10.2, algebra-tactics 1.2.7, coq-lsp 0.2.5+9.1 (for `pet`). Pin exactly in the Dockerfile (like eulerian) and with `>= 1.16.0 & < 1.17` style bounds in the `.opam` (like icones/qbs); record the validated snapshot in a comment (like prime-gap).
2. **Reals via mathcomp-analysis `R : realType`, probability self-contained and finite.** Chernoff needs `exp`, so pure `rat` (the graph-theory-rocq trick) is not enough; mathcomp-analysis is what the org uses for reals (qbs, icones) and what `mathcomp-skills` documents (domains 42–44). Keep the probability layer *finite* (a distribution on a `finType` is `p : T -> R` with `\sum_(x : T) p x = 1`, expectation is a bigop) so we only need `reals`, `exp` (for `expR`) and bigop lemmas, not the Lebesgue integral — mirroring the Lean "minimal layer". Do not depend on infotheo (nobody in the org does; two reals libraries would fight).
3. **Asymptotics stated finitely**, in the style of `GTBase.asymptotics` (`eventually`, explicit constants): "O(log n) rounds w.h.p." becomes `exists C N, forall n, N <= n -> Pr[T_n > C * trunc_log 2 n] <= 1 / n%:R` (or `<= n%:R^-1`), no limits.
4. **Layout = digraph-theory + qbs**: `theories/` with strict layers listed in `_CoqProject`, one `prelude.v` with smoke lemmas, coq-community thin Makefile, `rocq-<name>.opam`, gating `build.yml` + separate `blueprint.yml`, `verify.sh` for `Print Assumptions`, rocqblueprint with `\rocq{Ns.file.lemma}` links mirroring the Lean blueprint chapter structure.
5. **Agent setup = the org's plugins + a small repo CLAUDE.md** (the repos have none, but that is because the maintainers rely on user-level plugins; since our sandbox is a container, put the essentials in the repo and mount/bake the plugins).

### 3.2 Layout

```
rocq-dynamics/
├── _CoqProject
├── Makefile                          # coq-community thin wrapper (copy of digraph-theory's)
├── rocq-dynamics.opam
├── Dockerfile                        # eulerian-style agent image (Rocq + MC + analysis + coq-lsp + rocq-mcp + claude)
├── verify.sh                         # clean rebuild + Print Assumptions of headline theorems
├── .mcp.json                         # rocq-mcp stdio server (project-scoped)
├── CLAUDE.md                         # short; points to docs/DESIGN.md and PLAN.md
├── .claude/settings.json             # hooks: layering check + admitted grep (optional; plugins do the rest)
├── .gitignore
├── README.md  CHANGELOG.md  CONTRIBUTING.md
├── docs/
│   ├── DESIGN.md                     # ecosystem survey (Reuse/Build table), decisions D1.., layers
│   ├── PLAN.md                       # milestones M0..; Lean-file → Rocq-file map; per-lemma status
│   ├── LEAN_TO_ROCQ.md               # dictionary: Mathlib name → MathComp/analysis name (search results)
│   └── formal/                       # optional: eulerian-style PDF + extract_catalog.py
├── blueprint/src/{web,print,content}.tex, macros/, plastex.cfg, ch_*.tex
├── scripts/
│   ├── axiom_audit.py                # from digraph-theory (probe file of Print Assumptions)
│   ├── check_layers.py               # from icones (adapt LAYERS)
│   └── oracle/                       # Python Monte-Carlo / exact small-n oracle + pytest
├── lean/                             # (optional) the Lean source as read-only reference, or a git submodule
└── theories/
    ├── prelude.v                     # imports, options, smoke lemmas
    ├── prob/  finprob.v              # finite distributions on finType: dist, Pr, Ex, indep, product
    ├── prob/  bounds.v               # Markov, Chebyshev (finite), self-contained Chernoff (expR)
    ├── prob/  concentration.v        # union bound, w.h.p. wrapper, eventually/O-notation
    ├── dyn/   rumor.v                # push protocol on K_n, round r.v., O(log n) w.h.p.
    ├── dyn/   majority.v             # 3-majority, consensus w.h.p.
    └── main.v                        # headline theorems re-exported with their informal statements
```

### 3.3 Exact file contents

**`_CoqProject`**
```
-R theories Dynamics
-arg -w -arg -notation-overridden,-ambiguous-paths
-arg -w -arg -deprecated-since-mathcomp-analysis-1.9.0
-arg -w -arg -deprecated-since-mathcomp-2.5.0

# Layers (enforced by scripts/check_layers.py): prelude < prob < dyn < main.
# A file may only Require files in a strictly lower layer or its own layer.

# -- prelude ------------------------------------------------------------
theories/prelude.v

# -- prob: finite probability + concentration ---------------------------
theories/prob/finprob.v
theories/prob/bounds.v
theories/prob/concentration.v

# -- dyn: the two dynamics ---------------------------------------------
theories/dyn/rumor.v
theories/dyn/majority.v

# -- main ---------------------------------------------------------------
theories/main.v
```

**`Makefile`** (verbatim pattern from `digraph-theory/Makefile`)
```make
# Thin wrapper delegating to a Makefile.coq generated from _CoqProject.
# (Standard coq-community pattern. Works with `coq_makefile` / `rocq makefile`.)
KNOWNTARGETS := Makefile.coq
KNOWNFILES   := Makefile _CoqProject
.DEFAULT_GOAL := invoke-coqmakefile

Makefile.coq: Makefile _CoqProject
	$(COQBIN)rocq makefile -f _CoqProject -o Makefile.coq $(EXTRA_DIR_OPTS)

invoke-coqmakefile: Makefile.coq
	$(MAKE) --no-print-directory -f Makefile.coq $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

clean:: Makefile.coq
	$(MAKE) --no-print-directory -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

# Project-specific gates
.PHONY: invoke-coqmakefile clean layers admitted axioms gate $(KNOWNFILES)
layers:
	python3 scripts/check_layers.py
admitted:
	@! grep -rnE '^\s*(Admitted|admit)\.' theories/ || (echo "Admitted found"; exit 1)
axioms: invoke-coqmakefile
	python3 scripts/axiom_audit.py
gate: layers invoke-coqmakefile admitted axioms

%: invoke-coqmakefile
	@true
```

**`rocq-dynamics.opam`**
```
opam-version: "2.0"
name: "rocq-dynamics"
version: "dev"
synopsis: "Opinion dynamics on the complete graph in Rocq/MathComp: rumor spreading and 3-majority w.h.p."
description: """
Port of a Lean 4 + Mathlib development: a minimal finite-probability layer with a
self-contained Chernoff bound, rumor spreading on K_n in O(log n) rounds w.h.p., and
3-majority consensus w.h.p. Built on MathComp and mathcomp-analysis (reals).
"""
maintainer: "Emanuele Natale <emanuele.natale@inria.fr>"
authors: ["Emanuele Natale" "Marc Lelarge"]
license: "Apache-2.0"
homepage: "https://github.com/<org>/rocq-dynamics"
bug-reports: "https://github.com/<org>/rocq-dynamics/issues"
dev-repo: "git+https://github.com/<org>/rocq-dynamics.git"

build: [[ make "-j%{jobs}%" ]]
install: [[ make "install" ]]

depends: [
  # Validated snapshot (see Dockerfile): Rocq 9.1.1, MathComp 2.5.0, classical/analysis 1.16.0,
  # HB 1.10.2, algebra-tactics 1.2.7. Bounds follow icones-rocq / mathcomp-qbs.
  "rocq-core"                 { >= "9.1" & < "9.2~" }
  "rocq-mathcomp-ssreflect"   { >= "2.5.0" & < "2.6~" }
  "rocq-mathcomp-fingroup"    { >= "2.5.0" & < "2.6~" }
  "rocq-mathcomp-algebra"     { >= "2.5.0" & < "2.6~" }
  "rocq-mathcomp-classical"   { >= "1.16.0" & < "1.17~" }
  "rocq-mathcomp-analysis"    { >= "1.16.0" & < "1.17~" }
  "rocq-hierarchy-builder"    { >= "1.10.0" }
  "coq-mathcomp-algebra-tactics" { >= "1.2.7" }
]
tags: [ "logpath:Dynamics" "keyword:probability" "keyword:opinion dynamics" "keyword:Chernoff" ]
```

**`Dockerfile`** (adapted from `mathcomp-eulerian/Dockerfile`; `podman build -t rocq-dynamics-claude .`)
```dockerfile
# syntax=docker/dockerfile:1
# Rocq 9.1.1 + MathComp 2.5.0 + classical/analysis 1.16.0 + coq-lsp (pet) + rocq-mcp + Claude Code.
FROM mathcomp/mathcomp:2.5.0-rocq-prover-9.1
USER root
RUN apt-get update && apt-get install -y --no-install-recommends \
      curl ca-certificates git make m4 pkg-config libgmp-dev ripgrep jq \
      python3 python3-venv python3-pip \
 && curl -fsSL https://deb.nodesource.com/setup_20.x | bash - \
 && apt-get install -y --no-install-recommends nodejs && rm -rf /var/lib/apt/lists/*
RUN npm install -g @anthropic-ai/claude-code
USER coq
RUN opam update \
 && opam install -y \
      rocq-mathcomp-classical.1.16.0 rocq-mathcomp-analysis.1.16.0 \
      coq-mathcomp-algebra-tactics.1.2.7 rocq-hierarchy-builder.1.10.2 \
      coq-lsp.0.2.5+9.1 \
 && opam clean -a -c -s --logs
RUN echo 'eval $(opam env)' >> ~/.profile && echo 'eval $(opam env)' >> ~/.bashrc
# rocq-mcp in a venv (pin the commit as eulerian's pyproject does)
RUN python3 -m venv /home/coq/rocq-mcp-venv \
 && /home/coq/rocq-mcp-venv/bin/pip install --no-cache-dir "git+https://github.com/LLM4Rocq/rocq-mcp@<commit>"
USER root
RUN mkdir -p /etc/claude && printf '%s\n' \
 '{"mcpServers":{"rocq-mcp":{"type":"stdio","command":"/home/coq/rocq-mcp-venv/bin/rocq-mcp","args":[],' \
 '"env":{"ROCQ_COQC_TIMEOUT":"120","ROCQ_VERIFY_TIMEOUT":"240"}}}}' > /etc/claude/mcp.json
USER coq
WORKDIR /workspace
ENTRYPOINT ["/bin/bash","-lc","exec claude --mcp-config /etc/claude/mcp.json \"$@\"","--"]
```
Notes: the `mathcomp/mathcomp:2.5.0-rocq-prover-9.1` tag is the one digraph-theory's CI uses
("tag existence verified on Docker Hub"); its user is `coq` (check with `podman run --rm -it --entrypoint id <img>`
and adjust `USER`). If the image's opam repo lacks `coq-lsp.0.2.5+9.1`, add
`opam repo add coq-released https://coq.inria.fr/opam/released` first (eulerian does this). Run
as eulerian's header says: `podman run --rm -it -v "$PWD":/workspace -v "$HOME/.claude":/home/coq/.claude rocq-dynamics-claude`
(eulerian adds `--dangerously-skip-permissions`; the guardrails hook then blocks push/amend/reset).

**`.mcp.json`** (for runs outside the image; pattern from `mathcomp-eulerian/plugin/rocq/.mcp.json`)
```json
{ "mcpServers": { "rocq-mcp": { "type": "stdio", "command": "uvx", "args": ["rocq-mcp"],
  "env": { "ROCQ_COQC_TIMEOUT": "120", "ROCQ_VERIFY_TIMEOUT": "240" } } } }
```

**`.github/workflows/build.yml`** (gating; digraph `ci.yml` + icones `build.yml`)
```yaml
name: Build
on: { push: { branches: [main] }, pull_request: { branches: [main] }, workflow_dispatch: }
permissions: { contents: read }
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v5
      - name: Check import layering (cheap, before the toolchain)
        run: python3 scripts/check_layers.py
      - name: No Admitted / admit / Axiom in theories
        run: "! grep -rnE '^\\s*(Admitted|admit)\\.|^\\s*(Axiom|Parameter|Conjecture|Hypothesis)\\s' theories/"
      - uses: coq-community/docker-coq-action@v1
        with:
          custom_image: 'mathcomp/mathcomp:2.5.0-rocq-prover-9.1'
          install: |
            startGroup "Install dependencies"
              opam install -y rocq-mathcomp-classical.1.16.0 rocq-mathcomp-analysis.1.16.0 \
                              coq-mathcomp-algebra-tactics.1.2.7
            endGroup
          before_script: |
            startGroup "Workaround permission issue"
              sudo chown -R "$(id -u):$(id -g)" .
            endGroup
          script: |
            startGroup "Build"
              make -j2
            endGroup
            startGroup "Axiom audit (Print Assumptions on headline theorems)"
              ./verify.sh
            endGroup
          after_script: |
            sudo chown -R 1001:116 .
```
Add a second `blueprint.yml` copied from `mathcomp-eulerian/.github/workflows/blueprint.yml`
(coqdoc job with `make -f CoqMakefile html`, `pip install rocqblueprint; cd blueprint/src; rocqblueprint web`,
combine into `site/` with coqdoc at `site/doc/`, `actions/deploy-pages@v4`).

**`verify.sh`** (icones pattern)
```bash
#!/usr/bin/env bash
# Clean rebuild + Print Assumptions of the headline theorems. Expected: only the three
# mathcomp-classical axioms (boolp.functional_extensionality_dep, boolp.propositional_extensionality,
# boolp.constructive_indefinite_description). No project Axiom/Parameter/Admitted.
set -e; cd "$(dirname "$0")"
make clean && make -j
printf '%s\n' 'From Dynamics Require Import main.' \
  'Print Assumptions rumor_spreading_whp.' \
  'Print Assumptions three_majority_consensus_whp.' \
  'Print Assumptions chernoff_upper.' \
  | rocq repl -q -Q theories Dynamics
```

**`theories/prelude.v`** (digraph `prelude.v` + qbs header style)
```coq
(** * Dynamics.prelude — shared imports, options and smoke checks

    Every other file starts with [From Dynamics Require Import prelude.].
    Reals come from mathcomp-analysis ([R : realType]); classical logic from
    [boolp]. Probability is FINITE throughout: a distribution on a [finType]
    is a function to [R] summing to 1, expectation is a [\sum_]. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From mathcomp Require Import boolp classical_sets reals exp.
From mathcomp.algebra_tactics Require Import ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.

(** ** Smoke checks: a broken toolchain fails at [make] time. *)
Lemma prelude_classical (P : Prop) : P \/ ~ P.
Proof. by case: (pselect P); [left | right]. Qed.
Lemma prelude_reals (R : realType) : (0 : R) < 1. Proof. exact: ltr01. Qed.
Lemma prelude_expR (R : realType) : expR (0 : R) = 1. Proof. exact: expR0. Qed.
```

**`CLAUDE.md`** skeleton (synthesizing `rocq-skills` SKILL.md rules, digraph `CONTRIBUTING.md`, eulerian README "Conventions")
```markdown
# rocq-dynamics — instructions for coding agents

Read `docs/DESIGN.md` (layers, representation decisions) and `docs/PLAN.md` (milestones,
Lean→Rocq file map) before touching `theories/`. The Lean source in `lean/` is the spec.

## Toolchain (inside the container; never install things ad hoc)
Rocq 9.1.1, MathComp 2.5.0, mathcomp-classical 1.16.0, mathcomp-analysis 1.16.0, HB 1.10.2,
algebra-tactics 1.2.7. `eval $(opam env)` is preloaded. rocq-mcp is available as MCP tools.

## Build & gates
- `make -j` builds everything in `_CoqProject` (add new files there, in layer order).
- `make gate` = layering check + build + no-Admitted grep + `Print Assumptions` audit. Run before
  every checkpoint commit. `./verify.sh` is the canonical headline audit.
- Allowed axioms: only `boolp.functional_extensionality_dep`, `boolp.propositional_extensionality`,
  `boolp.constructive_indefinite_description`. No `Axiom`, `Parameter`, `Admitted`, `admit`
  on `main`. Temporary `Admitted` is fine on a branch but must be listed in `docs/PLAN.md`.

## Proving workflow (MCP-first)
1. `rocq_toc`/`rocq_start(file, theorem)` to see the goal; `rocq_query("Search ...")` before
   writing tactics — MathComp/analysis probably has it (check `docs/LEAN_TO_ROCQ.md` first, and
   add every Mathlib→MathComp correspondence you discover there).
2. `rocq_step_multi` to test candidates, `rocq_check` to commit, `rocq_compile_file` as the file gate,
   `make` as the project gate. `rocq_assumptions` on any new top-level theorem.
3. Never change a theorem statement to make it provable. If a statement is wrong, stop and write
   the issue in `docs/PLAN.md`. Never weaken w.h.p. exponents or constants silently.
4. Stage only files you touched; commit often (`checkpoint: ...`); never push, amend, or reset.

## Style (MathComp house style; `mathcomp-skills` is the reference)
- `From Dynamics Require Import prelude.` first; `Section` + `Variable R : realType`;
  `Implicit Types`; 80-char lines; ssreflect tactics, `by`/`exact:` closers.
- Names: `mainSymbol_suffixes` (`Pr_union_le`, `Ex_sum`, `chernoff_upper`, `rumor_round_le`);
  lowercase file names. One `(** ... *)` docstring per public lemma, quoting the Lean name it ports
  (`(** Port of [Mathlib.Probability....] / Lean [rumor_whp]. *)`).
- Finite probability only: `dist T := {p : T -> R | \sum_(x : T) p x = 1}`-style; probabilities and
  expectations are `\sum_` bigops; asymptotics are `eventually`/explicit constants, no limits.
- Prefer `lra`/`ring`/`nra` (algebra-tactics) for real arithmetic; `lia` (with zify) for nat.

## Deliverables besides code
Update `CHANGELOG.md` per milestone; keep `blueprint/src/ch_*.tex` in sync
(`\rocq{Dynamics.file.lemma}`, `\rocqok`, `\uses{}`); keep `docs/PLAN.md` status table current.
```

**`.claude/settings.json`** (optional repo hooks; the org's PostToolUse audit hook from
`mathcomp-skills/hooks/hooks.json` is the model)
```json
{ "hooks": { "PostToolUse": [ { "matcher": "Edit|Write",
    "hooks": [ { "type": "command", "timeout": 15,
      "command": "f=$(jq -r .tool_input.file_path); case \"$f\" in *.v) grep -nE '^\\s*(Admitted|admit)\\.' \"$f\" | sed 's/^/ADMITTED: /' ;; esac; exit 0" } ] } ] } }
```
and install the two org plugins user-side (or bake into the image): `git clone https://github.com/LLM4Rocq/mathcomp-skills ~/.claude/skills/mathcomp-skills`
and the `rocq` plugin from `rocq-skills` (provides `/rocq:prove`, `/rocq:autoprove`, `/rocq:checkpoint`, guardrails).

**`.gitignore`** (union of digraph/qbs/icones)
```
*.vo *.vok *.vos *.glob *.aux .*.aux .coq-native/ .lia.cache .nia.cache
Makefile.coq Makefile.coq.conf .Makefile.coq.d Makefile.conf .Makefile.d
_opam _build/ __pycache__/ *.pyc .venv/
rocq_mcp_cache_*.v .tmp*
.claude/ .vscode/ *~ .DS_Store
blueprint/src/web/ blueprint/src/print/ html/ site/
```

**Blueprint** (`blueprint/src/web.tex`, from eulerian)
```latex
\documentclass{report}
\usepackage{amssymb, amsthm, amsmath, hyperref}
\usepackage[dep_graph]{blueprint}
\input{macros/common}\input{macros/web}
\home{https://<org>.github.io/rocq-dynamics/}
\github{https://github.com/<org>/rocq-dynamics}
\dochome{https://<org>.github.io/rocq-dynamics/doc}
\title{Rumor spreading and 3-majority on $K_n$ — a Rocq/MathComp formalization}
\begin{document}\maketitle\input{content}\end{document}
```
with `plastex.cfg` = `[general] renderer=HTML5 copy-theme-extras=yes plugins=plastexdepgraph rocqblueprint` and result blocks
`\begin{theorem}[Chernoff, upper tail]\label{thm:chernoff_upper}\uses{def:dist,lem:markov}\rocq{Dynamics.prob.bounds.chernoff_upper}\rocqok ...`.
Mirror the Lean blueprint's chapters one-to-one so the dependency graph is comparable.

### 3.4 Process recommendations distilled from the exemplars

- Start like `mathcomp-kummer`: a `blueprint_plan.md`-style plan that already contains the init shell recipe, then the smallest compiling skeleton (`prelude.v` with smoke lemmas) *before* any mathematics — the org's plans all note "smoke-checked: `make` builds".
- Write `docs/DESIGN.md` with the digraph "Need / Already exists? / Verdict" table: for each Lean/Mathlib ingredient (PMF, `∑`, `exp`, `Finset.card`, Chernoff, `Nat.log`) record the MathComp/analysis counterpart found via `rocq_query`; this is the Lean→Rocq dictionary agents will search first.
- Statement-first: port every Lean theorem *statement* first (Admitted), get the file compiling, review faithfulness against the Lean (the org's `DEFINITIONS_AUDIT.md` / `SPEC_TO_PAPER.md` habit), then let `/rocq:autoprove` fill, with the header fence protecting statements.
- Keep a Python oracle (`scripts/oracle/`) that simulates both dynamics and checks small-n exact probabilities against the Rocq definitions where they compute (digraph's cross-check rule), and pytest it in CI.
- Use two workflows: gating build+audit vs non-blocking docs; fail CI on `git diff --exit-code` for regenerated artifacts; publish coqdoc + blueprint + (optionally) a formal PDF to Pages.
- Be honest in README about machine authorship and axiom budget (prime-gap WARNING, qbs "Limitations", icones "Fully axiom-free" sections).
