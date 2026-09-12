# LLM-for-Rocq tooling cited by the ChatGPT answer — compatibility with Rocq 9.1.1 + MathComp 2.5 + rocq-mcp

Stack under evaluation: Rocq 9.1.1, MathComp 2.5.0, mathcomp-analysis 1.16.0, LLM4Rocq `rocq-mcp` (petanque / coq-lsp 0.2.5+9.1), Claude Code agents. Date: 2026-09-12.

## 1. ITPEval (arXiv 2607.19407, Wu / George / Anandkumar, Jul 2026) — VERDICT: benchmark only

- Code: https://github.com/lean-dojo/ITPEval (MIT, public, 2 commits, last 2026-07-08). Data: HF `jiayi005/ITPEval` (CC BY 4.0).
- What it is: a *translation* benchmark (Lean4 <-> Rocq <-> Isabelle <-> HOL Light, 12 directed pairs; 1,560 statement records + 296 proof records, 74 per prover). Not a prover, no proof-search loop, no fine-tuned model.
- Rocq harness: `itpeval/provers/rocq/install.sh` creates an opam switch with `ROCQ_VERSION="${ROCQ_VERSION:-9.0.0}"` (overridable) and installs `rocq-prover`; `check.sh` just compiles `hello.v` "with `rocq` or `coqc`". Paper's Rocq backend = "persistent REPL workers with Reset Initial". No coq-lsp / petanque. Nothing MathComp-specific (MathComp appears only in third-party licences).
- Usable pieces for us: none beyond what rocq-mcp already gives (`rocq_compile`). Headline numbers are useful only as a sanity check: proof translation into Rocq is hard even for frontier models (best: GPT-5.5, 29.1 % statements / 10.5 % proofs).

## 2. Rango (arXiv 2412.14063, ICSE 2025, Thompson et al.) — VERDICT: not compatible with Rocq 9.1 (Coq 8.18 pinned), heavy, research artifact

- Code: https://github.com/rkthomps/coq-modeling (MIT, 561 commits, last commit 2026-02-23 "Update instructions for downloading Rango model"); data/benchmark: https://github.com/rkthomps/CoqStoq (last 2026-04-27). Zenodo artifact DOI 10.5281/zenodo.14853833.
- Coq version: hard-pinned by `CoqStoq/coqstoq.opam` -> `"coq.8.18.0"`, `"coq-core.8.18.0"`, `"coq-lsp.0.2.0+8.18"`, `"coq-mathcomp-ssreflect.2.2.0"` (+ algebra/field/fingroup/solvable 2.2.0). Paper: "Rango, Tactician, and Proverbot all use Coq 8.18". No 9.x anywhere; Dockerfile imports that switch from `coq.inria.fr/opam/released`.
- Interface: coq-lsp via the CoqPyt Python client (sr-lab/coqpyt, git submodule, last commit 2026-05-03) — i.e. the same LSP family as rocq-mcp but an older API (no petanque).
- Model: fine-tuned DeepSeek-Coder 1.3B (trained on 4x A100); inference needs a GPU ("allocated a single NVIDIA" GPU per run). Plus a dense retriever + reranker (also trained). No API-model fallback: it's a local-model pipeline.
- ssreflect: CoqStoq's training/test set *does* include MathComp/ssreflect-style projects (FourColor is a benchmark project, 1,341 theorems; mathcomp libs in the switch), so the model has seen ssreflect syntax. But results are per-tactic-step retrieval for a 1.3B model — far below a frontier model + rocq-mcp on MathComp-analysis-style goals. Paper reports 32.0 % on CoqStoq test overall.
- Porting to 9.1 would mean re-mining CoqStoq under Rocq 9.1 + rebuilding 2,226 projects + retraining. Not a plausible add-on for us.

## 3. Quarry (arXiv 2606.17981, "Planning to Hammer", Zhang et al., Jun/Jul 2026) — VERDICT: not compatible with Rocq 9.1 (SerAPI dependency); the *idea* is portable

- Code: https://github.com/ningZhang-cs/QUARRY (Apache-2.0, 1 commit, 2026-07-11, 0 stars). Ships recursive decomposition runner, difficulty-ranking model, CoqHammer glue, three benchmarks (CoqGym100, Wigderson100, TransBench58 = Rust/Verus->Rocq). README: "does not support arbitrary user projects out-of-the-box".
- Versions (README, verbatim): `coq.8.20.1`, `coq-serapi.8.20.0+0.20.0`, `coq-hammer.1.3.2+8.20`; benchmarks declare Coq 8.10/8.11, 8.13, 8.20. LLMs: GPT-5.2 (main), GPT-5.4, Claude Sonnet 4.6, MiniMax-M2.5, DeepSeek-v3.2 via OpenRouter.
- Blocking issue: built on **SerAPI**, which is dead — ejgallego/coq-serapi (now under rocq-archive): "Coq SerAPI has now stopped development, the 0.20 release for Coq 8.20 will be the last managed by us ... succeeded by coq-lsp". Latest opam `coq-serapi.8.20.0+0.20.0` requires `coq >= "8.20" & < "8.21"`. There is no SerAPI for Rocq 9.x. Rewriting Quarry's Rocq layer on petanque is possible but is a fork, not an install.
- CoqHammer itself IS available for our stack: opam `coq-hammer.1.3.3+9.1` (rocq-prover/opam released, dated 2026-07-06) depends on `"coq" {>= "9.1" & < "9.2~"}` + `coq-hammer-tactics` (same version); also `1.3.3+9.2`, `1.3.2+9.0`. No `rocq-hammer` package exists. Upstream branches `rocq-9.0/9.1/9.2` active (rocq-9.1 last commit 2026-07-06). Needs >= 1 external ATP: Vampire, E, Z3, CVC4/cvc5 (system binaries, not opam).
- CoqHammer x MathComp — known weak: CoqHammer `TODO.md` item 1: "Make boolean reflection work. Make CoqHammer usable with MathComp: this will probably require much more than just making boolean reflection work". The `mathcomp` branch is dead (last commit 2019-01-21). palmskog (Rocq Discourse, 2020): "CoqHammer has some limited support for MathComp and proofs by reflection out of the box"; workaround for arithmetic: `zify` (mczify) then `hammer`. Expect `hammer` to be near-useless on `\sum_(i in A) ...`, canonical-structure-heavy or `mathcomp-analysis` (`\bar R`, measures, `lim`) goals; `sauto`/`hauto` can still close small propositional/first-order leaves after `move=> /andP [..]`-style unpacking, and `lia` after `zify` is the practical hammer for nat/int arithmetic.

## 4. Other non-LLM4Rocq tooling, Rocq 9.x status (brief)

- **CoqPilot** (JetBrains-Research/coqpilot, v2.4.3, last commit 2026-04-15): VS Code-only, no CLI/headless mode; README: "`coq-lsp` version `0.2.2+8.19` is currently required"; providers = OpenAI, LM Studio, JetBrains Grazie (no Anthropic). The RocqStar agent (AAMAS'26, arXiv 2505.22846) is their research pipeline, not a shipped tool. Verdict: **not compatible with Rocq 9.1**, and it duplicates what Claude Code + rocq-mcp does.
- **Tactician** (coq-tactician): opam packages stop at `coq-tactician.1.0~beta2.1+8.19`; changelog: "Available for all Coq versions between v8.12 and v8.18"; no Rocq 9 branch. Graph2Tac pinned to Coq 8.11. Verdict: **not compatible with Rocq 9.1**.
- **Proverbot9001** (UCSD-PL): SerAPI-based (`coq_serapy` submodule), last commit 2024-05-16, Coq 8.x. Verdict: **unmaintained / incompatible**.
- **coq-lsp / rocq-lsp + petanque** (ejgallego, rocq-community/rocq-lsp): the only maintained programmatic Rocq 9.x interface; this is what rocq-mcp already wraps (0.2.5+9.1). Nothing extra to add.
- **Rocq-MCP + Opus** (arXiv 2603.20405, Putnam 2025 in Rocq) and **RocqSmith** (arXiv 2602.05762, agent-prompt optimisation) are the closest published workflows to ours; both build on the same rocq-mcp/petanque layer.

## Recommendation

1. Keep rocq-mcp + Claude Code as the backbone. Every alternative cited is either Coq 8.x-pinned (Rango 8.18, Quarry 8.20 via dead SerAPI, CoqPilot 8.19, Tactician <= 8.19, Proverbot) or a benchmark (ITPEval). None is a drop-in for Rocq 9.1 + MathComp 2.5.
2. Cheap, worth trying now: install `coq-hammer.1.3.3+9.1` (+ `coq-hammer-tactics`, + an ATP such as `eprover`/`vampire`/`z3` on PATH) into the 9.1 switch and expose `sauto`/`hauto`/`hammer` as leaf tactics the agent may try via `rocq_run_tactic`. Set expectations: good for propositional/first-order leftovers and (after `zify`) arithmetic; do not expect it to touch big-operator, canonical-structure or mathcomp-analysis goals. Measure the hit-rate on a few dozen stuck subgoals before institutionalising it.
3. Borrow Quarry's *method*, not its code: have the agent propose 2–3 decompositions into `Admitted` sublemmas, type-check them with rocq-mcp, then recurse — already natural in Claude Code with a "sketch, admit, then discharge" prompt. Quarry's ranking model (hammer-solvability) is irrelevant for us because hammer rarely fires on MathComp goals.
4. Rango-style retrieval can be replaced for free by MathComp's own `Search`/`rocq_search`-type queries and by keeping local `.v` files in the agent context; a 1.3B local model is not worth a GPU here.
5. Revisit only if (a) SerAPI-free ports of Quarry appear, (b) CoqHammer's boolean-reflection/MathComp work resumes (watch `lukaszcz/coqhammer` `booltransl`/`mathcomp` branches), or (c) CoqStoq is re-mined for Rocq 9.x.
