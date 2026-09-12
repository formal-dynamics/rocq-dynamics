# LLM4Rocq tooling survey (2026-09-10)

Survey of the *tooling* repositories of <https://github.com/LLM4Rocq> (Inria), done before
starting the Rocq port of [leanamycs](https://github.com/formal-dynamics/leanamycs). Read from
shallow clones on 2026-09-10; "last commit" = HEAD date of the clone. Companion document:
[`llm4rocq-projects.md`](llm4rocq-projects.md) (how the org lays out formalization repos).

## 0. Executive summary

| Fact | Evidence |
|---|---|
| The org standardises on one toolchain: **Rocq 9.1.1, MathComp 2.5.0, MathComp-Analysis 1.16.0, HB 1.10.2, coq-lsp 0.2.5+9.1 (ships `pet`/`pet-server`), algebra-tactics 1.2.7, zify 1.6.0+2.3+8.18, OCaml 5.2**. | `mathcomp-skills/.github/workflows/citations.yml`, `mathcomp-skills/skills/mathcomp-skills/LAST_VERIFIED.md`, `rocq-mcp-evolve/repro/opam-packages.txt`, `Putnam2025-Rocq/README.md`, `small-prime-gap/coq-prime-gap.opam`, `mathcomp-eulerian/Dockerfile` |
| The agent stack is three layers: `pytanque` (Python ↔ petanque JSON-RPC) → `rocq-mcp` (13 MCP tools, Python/FastMCP) → two Claude Code plugins, `rocq-skills` (workflow `/rocq:prove`, `/rocq:autoprove`, …) and `mathcomp-skills` (MathComp style guide + `/mathcomp-review`). | `rocq-mcp/pyproject.toml` pins `pytanque @ git+…@v0.2.2`; both plugins hard-code tool names `mcp__rocq-mcp__rocq_*` |
| Proof of viability: `mathcomp-qbs` (9,043 lines, 414 proofs, 0 Admitted, written by Claude with rocq-mcp), `Putnam2025-Rocq` (12/12), `mathcomp-eulerian`, `small-prime-gap`, `icones-rocq` (75k lines). | their READMEs |
| Install traps (verified): `rocq-mcp` is **not on PyPI** (HTTP 404), so `uvx rocq-mcp` / `pipx install rocq-mcp` in the READMEs do not work; PyPI's `pytanque` 1.1.0 is an **unrelated package** (Quarkslab/arybo). Install both from git, as `mathcomp-eulerian/Dockerfile` does. | `curl https://pypi.org/pypi/rocq-mcp/json` → 404 |
| `rocq-mcp-evolve` is a second, independent MCP server (OCaml, in-process Rocq, 8 tools, benchmarked). The skills do not know its tools; optional. | `rocq-mcp-evolve/README.md` |
| `rocqet-search` gives a hosted semantic search over MathComp (19,448 declarations with NL descriptions) as an MCP tool, zero infrastructure. | `rocqet-search/README.md` |
| The remaining repos (rocq-ml-toolbox, Pile-of-rocq, LLM4Docq, deep-premise-research, crrrocq(-mini), nlir, babel-formal) are ML-training / dataset / research pipelines, not needed for interactive proving. babel-formal's finding (frontier LLM + interactive repair reaches 82.9 % Lean→Rocq on their benchmark; only 16–33 % for vanilla→SSReflect) validates the plan and explains why `mathcomp-skills` exists. | their READMEs |

## 1. Repo by repo

### 1.1 `pytanque` — Python client for petanque (coq-lsp's machine protocol)
Thin client (`pytanque/client.py`) for **Petanque**, the JSON-RPC protocol inside coq-lsp. Transports: socket (`pet-server`, port 8765), stdio (spawns `pet`), HTTP (`rocq-ml-server`). Backbone of rocq-mcp, nlir, rocq-ml-toolbox, deep-premise-research, babel-formal. v0.2.2, last commit 2026-04-18; Python ≥ 3.10. Protocol types are generated from `protocol.atd` and must match the coq-lsp version (rocq-mcp's code cites `coq-lsp 0.2.5+9.1`). Install only from git: `pip install git+https://github.com/llm4rocq/pytanque.git`. API: `start(file, theorem)`, `run(state, cmd)`, `goals`, `premises`, `toc`, `ast`, `get_state_at_pos`, …

### 1.2 `rocq-mcp` — the MCP server Claude Code talks to (central piece)
Python (FastMCP) stdio server, **13 tools**, backed by `coqc` and, when `pet` is on PATH, by pytanque in stdio mode. LRU state table + import cache so heavy mathcomp imports are paid once. v0.3.1, last commit 2026-08-05, 30 test files, CI on Python 3.11/3.14. README is written for agents.

Deps: Python ≥ 3.11; `fastmcp>=3.1.0`, `psutil`, `pytanque @ git+…@v0.2.2`. Runtime: `coqc` on PATH (default `ROCQ_COQC_BINARY=coqc`; on Rocq 9 the shim comes from the `coq-core` opam package) and `pet` for interactive tools.

| Tool | Purpose |
|---|---|
| `rocq_compile(source)` | batch `coqc` of a string; on in-proof error returns `state_id` + goals |
| `rocq_compile_file(file, keep_vo, mode="full"|"vos", timing)` | whole-file `coqc`; multi-error walker; `mode="vos"` = statements-only pre-pass |
| `rocq_verify(proof, problem_name, problem_statement)` | sandboxed check that the proof proves the *given* statement (Module sandbox, forbidden-command scan, `Print Assumptions` whitelist incl. `mathcomp.classical.boolp.*`) |
| `rocq_query(command, preamble|file|from_state)` | `Search`/`Check`/`Print`/`About`/`Locate` |
| `rocq_assumptions(name, file)` | `Print Assumptions` → axiom list |
| `rocq_start(file+theorem | file+line+char | preamble)` | open interactive session → `state_id` + goals |
| `rocq_check(body, from_state)` | run tactics; returns `last_valid_state_id` on error, `proof_tactics` when done, `stale_warning` |
| `rocq_step_multi(tactics[≤20], from_state)` | try many tactics without advancing |
| `rocq_toc(file)` / `rocq_notations(statement, preamble)` | outline / notation resolution |
| `rocq_diag()` / `rocq_health()` / `rocq_switch(name)` | pet health & RSS / which opam switch & binaries / change switch |

Workspace resolution: walks up from the file for `_RocqProject`/`_CoqProject`/`dune-project`; parses `-Q/-R/-I` and an allow-list of `-arg`s; falls back to `ROCQ_WORKSPACE` (which, when set, constrains all paths). Env: `ROCQ_PET_TIMEOUT=30`, `ROCQ_QUERY_TIMEOUT_CAP=300`, `ROCQ_COQC_TIMEOUT=60`, `ROCQ_VERIFY_TIMEOUT=120`, `ROCQ_MAX_PET_RSS_MB=min(50 % RAM, 16384)`, `ROCQ_MAX_STATES=1000`, `ROCQ_DUNE_BUILD=1`.

Concurrency: one pet per server process; Claude Code keys MCP servers by name, so parallel sub-agents sharing a name share one pet. The README prescribes a **named pool**: `.claude/agents/rocq-prover-1.md … -N.md`, each with a uniquely named inline `mcpServers` entry (`command: rocq-mcp`, optional `env.ROCQ_WORKSPACE=<worktree k>`, `ROCQ_MAX_PET_RSS_MB`). Plugin sub-agents ignore `mcpServers` frontmatter, so the pool must be plain `.claude/agents/` files. Agent registry is snapshotted at session start.

Sub-agent briefing preamble recommended by the README (now in our `CLAUDE.md`):
```
Before any Write or `coqc` on a .v file:
  1. Consult project Rocq guidance (CLAUDE.md / Skill).
  2. For scratch iteration on a single proof, use rocq-mcp:
       rocq_start file=<…>.v theorem=<lemma>;  rocq_step_multi tactics=[...]   (NOT coqc /tmp/x.v)
  3. Use `coqc` only for full-project rebuilds, axiom audits, final verification.
```

### 1.3 `rocq-skills` — Claude Code plugin `rocq`: prove/review/golf workflow
Plugin (marketplace `rocq-skills`, plugin `rocq`, v0.1.0, Marc Lelarge, MIT): a **cycle engine** (Plan → Work → Checkpoint → Review → Replan → Continue/Stop), MCP-first search/tactics, axiom checks, git guardrails, four sub-agents. Last commit 2026-04-02. A copy is vendored in `mathcomp-eulerian/plugin/rocq/`.

Layout (`plugins/rocq/`): `skills/rocq/SKILL.md` + `references/` (cycle-engine, rocq-mcp-tools-api, compilation-errors, tactics-reference, proof-templates, proof-golfing, admitted-filling, axiom-elimination, compiler-guided-repair, coq-stdlib-guide, rocq-phrasebook, subagent-workflows); `commands/` (11); `agents/` admitted-filler-deep (opus), axiom-eliminator (opus), proof-golfer (opus), proof-repair (sonnet), all restricted to `mcp__rocq-mcp__rocq_{start,check,step_multi,compile,query,verify}`; `hooks/hooks.json`: SessionStart → `bootstrap.sh`, PreToolUse(Bash) → `guardrails.sh` (in a dir with `_CoqProject`/`CoqMakefile`/`*.v`: blocks `git push`, `commit --amend`, `gh pr create` under policy ask|allow|block; always blocks `checkout --`/`reset --hard`/`clean -f`/`restore`; overrides `ROCQ_GUARDRAILS_DISABLE=1`, one-shot `ROCQ_GUARDRAILS_BYPASS=1`, `ROCQ_GUARDRAILS_COLLAB_POLICY`); `lib/scripts/` admitted_analyzer.py, check_axioms.sh, smart_search.sh, find_golfable.py, find_usages.sh, parse_rocq_errors.py.

Commands `/rocq:<name>`: `draft` (Admitted skeletons from informal claims) · `formalize` (only place statements may change) · `autoformalize` · `prove [File.v] [--repair-only] [--deep=…]` (header fence: never edits statements) · `autoprove [--max-cycles=20 --max-total-runtime=120m --max-stuck-cycles=3 --batch-size=2 --commit=auto]` · `checkpoint` (compile touched files, `make -f CoqMakefile`, `check_axioms.sh`, Admitted count, commit touched files only, never pushes) · `review` · `refactor` · `golf` · `learn` · `doctor` (its rocq-mcp version check assumes PyPI, broken).

Quality gate = compiles, zero Admitted, standard axioms only, `rocq_verify` passes, no statement changes. Expected project layout: `_CoqProject`/`CoqMakefile` at root, `coq_makefile -f _CoqProject -o CoqMakefile && make -f CoqMakefile`, 80-col files, git. Its "standard axioms" list (`check_axioms.sh`) **omits `constructive_indefinite_description`**, so mathcomp-analysis proofs get flagged by that script (the MCP path `rocq_verify` and mathcomp-skills' `print-assumptions-check.sh` do whitelist the `boolp` trio).

### 1.4 `mathcomp-skills` — skill + plugin for idiomatic MathComp / Analysis
~10,000-line, version-stamped style guide, verified against Rocq 9.1.1 / mc 2.5.0 / analysis 1.16.0 / HB 1.10.2 (`LAST_VERIFIED.md`; minimum Rocq 9.0 / mc 2.4 / analysis 1.13). Plugin with one read-only command `/mathcomp-review [file.v …] | --scope=changed|project`, one read-only sub-agent `mathcomp-style-auditor`, a PostToolUse hook running `audit-quick.sh` on each edited `.v` (advisory), and weekly CI re-checking ~250 `file:line` citations. Last commit 2026-08-05. Apache-2.0.

Actual layout: `.claude-plugin/plugin.json` (no marketplace.json), `commands/`, `agents/`, `hooks/`, `skills/mathcomp-skills/{SKILL.md, reference.md (§1–§37), domains/ (§38–§47: matrix, polynomial, finset, int_rat, derive, measure, topology, algebra_tactics, tuple_perm_binomial, finfun), templates.md, phrasebook.md, proof-development.md, errors.md, playbook.md, scripts/}`. The README's flat layout and `paths: "**/*.v"` auto-attach claim are stale. `SKILL.md` assumes an MCP server registered exactly as `rocq-mcp`.

Sections that matter for us: §34 bigops (`\sum`, `eq_bigr`, `under eq_bigr do`, `bigID`, `bigD1`, `big_split`, `big_morph`, `reindex`, `exchange_big`, `big_ord_recl/recr`, `big_const`); §36 eqType→choiceType→countType→finType and the boolp trio; §37 `Search` discipline; §40 finset; §45 `ring`/`field`/`lra`/`nra` on the mathcomp hierarchy, `lia`/`nia` only with `From mathcomp Require Import zify`; §46 tuples/binomials; §47 `{ffun T -> R}`; §43 measure/probability (measure-theoretic `probability T R` only).

### 1.5 `rocq-mcp-evolve` — alternative OCaml MCP server
Links `rocq-runtime` 9.1 in-process; tool surface chosen by A/B experiments on `rocq-workbook`/`miniF2F-rocq`. Claims lower cost per solve than rocq-mcp at the sonnet tier and ~1 ms per step. Last commit 2026-07-09. Tools: `build`, `open`, `check`, `step`, `try{candidates≤8}`, `auto_close` (lia/lra/nra/nia/ring portfolio), `rollback`, `state`; error hints rewrite Lean-isms into Rocq. Install: `opam pin add rocq-mcp-evolve https://github.com/LLM4Rocq/rocq-mcp-evolve.git` (needs `rocq-runtime < 9.2`); binary `rocq-mcp-evolve` (STATUS.md's "`rocq-mcp` binary" is stale). Not used by the skills; optional later.

### 1.6 `rocq-ml-toolbox`, `Pile-of-rocq`, `LLM4Docq`, `deep-premise-research`, `crrrocq(-mini)`, `nlir`, `babel-formal`
ML pipelines: inference server over N `pet-server` workers (needs a patched rocq-lsp fork, images are Rocq 9.0), dataset generation (HF `theostos/pile-of-rocq`), LLM docstrings for MathComp (source of rocqet's descriptions), RL premise selection, CoT+RAG prover fine-tuning, the 2024 NLIR agent, and Lean↔Rocq translation research. Nothing to install for our purposes.

### 1.7 `rocqet-search` — semantic search over Rocq libraries (+ MCP)
`.v → extract → enrich (NL descriptions) → embed (MiniLM dense + BM25 sparse in Qdrant) → FastAPI → Next.js`, plus MCP. Live deployment = MathComp only (19,448 decls, 96 % described; stdlib/analysis "coming soon"). v0.1.0, last commit 2026-07-25. Tools: `rocqet_search(query, lib?, kind?, limit≤50)`, `rocqet_stats()`. Positioned as the semantic complement to rocq-mcp's exact `Search`. Hosted API on Render free tier (cold starts).

### 1.8 Org publications (`.github/profile/README.md`)
PPDL (ICML 2026); *Library Before Proof: Making LLM-Generated Rocq Usable by Mathematicians* (Baudart, Lelarge, ICML 2026 wksp); NLIR (NeurIPS 2024 MATH-AI); *MiniF2F in Rocq* (NeurIPS 2025 MATH-AI, arXiv:2503.04763); *Babel-Formal* (NeurIPS 2025 MATH-AI, hal-05342510); *Tacq* (JFLA 2026); *LLM4Docq* (Rocqshop@ITP 2025); *Putnam 2025 in Rocq using Opus 4.6 and Rocq-MCP* (arXiv:2603.20405).

## 2. Dependency map

```
coq-lsp 0.2.5+9.1 (pet, pet-server) ──► pytanque (STDIO / socket / HTTP)
                                            │
            ┌───────────────────────────────┼────────────────────────────┐
            ▼                               ▼                            ▼
      rocq-mcp (13 tools)          rocq-ml-toolbox (server, Docker)   nlir, crrrocq, babel-formal, …
      pins pytanque@v0.2.2                  │
   ┌────────┴────────┐               Pile-of-rocq ─► LLM4Docq ─► rocqet-search (API + rocqet-mcp)
   ▼                 ▼
rocq-skills     mathcomp-skills
(/rocq:*, agents, (style guide, /mathcomp-review, audit hook)
 guardrails)

rocq-mcp-evolve: independent OCaml MCP server.
```

## 3. What this means for a finite-probability / Chernoff project
1. Finite probability is not first-class in the org's tooling: mathcomp-skills covers the measure-theoretic `probability T R`; nothing uses infotheo. We model uniform averages over `finType`s ourselves (bigops, §34/§40/§47), as the Lean development does.
2. Chernoff needs `expR`/`ln` on reals → mathcomp-analysis `exp.v` (`expR_ge1Dx`, `ln_le`, …); discovery via `rocq_query` + `rocqet_search`.
3. Warm imports: `all_ssreflect`/`all_algebra`/analysis take seconds; `rocq_start(preamble=…)` + `rocq_step_multi` pay it once; keep probe file names stable.
4. SSReflect style is where models are weakest; mitigate with mathcomp-skills and `/mathcomp-review` before checkpoints.

## 4. What was installed on this machine (user level, 2026-09-10)
```bash
# opam 2.5.2 in ~/.local/bin; switch rocq-9.1.1 (default) = org snapshot, OCaml 5.2.1
opam install rocq-core.9.1.1 coq-core.9.1.1 rocq-stdlib.9.1.0 \
  rocq-mathcomp-{ssreflect,fingroup,algebra,solvable,field}.2.5.0 \
  rocq-mathcomp-{classical,reals,analysis}.1.16.0 rocq-mathcomp-finmap rocq-mathcomp-bigenough \
  rocq-hierarchy-builder.1.10.2 coq-mathcomp-algebra-tactics.1.2.7 coq-mathcomp-zify coq-lsp.0.2.5+9.1
# Python tools (uv, Python 3.13): rocq-mcp 0.3.1, rocqet 0.1.0, rocqblueprint 0.0.9
uv tool install "git+https://github.com/LLM4Rocq/rocq-mcp"
uv tool install "rocqet[mcp] @ git+https://github.com/LLM4Rocq/rocqet-search"
uv tool install rocqblueprint
# MCP servers, user scope (~/.claude.json)
claude mcp add -s user rocq-mcp -e ROCQ_COQC_TIMEOUT=120 -e ROCQ_VERIFY_TIMEOUT=240 \
  -- ~/.local/bin/opam exec --switch=rocq-9.1.1 -- ~/.local/bin/rocq-mcp
claude mcp add -s user rocqet -e ROCQET_API_URL=https://rocqet-api.onrender.com -- ~/.local/bin/rocqet-mcp
# Plugins, user scope
claude plugin marketplace add LLM4Rocq/rocq-skills && claude plugin install rocq@rocq-skills
#   mathcomp-skills has no marketplace.json: wrapped in ~/.claude/local-marketplaces/llm4rocq-local
claude plugin marketplace add ~/.claude/local-marketplaces/llm4rocq-local
claude plugin install mathcomp-skills@llm4rocq-local
```

## 5. Pitfalls (from READMEs / code)
1. `uvx rocq-mcp` / `pipx install rocq-mcp` do not work (not on PyPI); install from git.
2. `pip install pytanque` installs the wrong package; use `git+https://github.com/LLM4Rocq/pytanque@v0.2.2`.
3. The MCP server must be named exactly `rocq-mcp`; both plugins hard-code `mcp__rocq-mcp__rocq_*`. Pool members need other names.
4. Opam switch drift: the server inherits PATH from whatever launched Claude; we pin with `opam exec --switch=rocq-9.1.1 --`; verify via `rocq_health`.
5. `coqc` on Rocq 9 comes from the `coq-core` compat package (or set `ROCQ_COQC_BINARY`).
6. Verified pair: pytanque v0.2.2 ↔ coq-lsp 0.2.5+9.1 on Rocq 9.1.1. The released coq-lsp requires `rocq-core >= 9.1 < 9.2`, which is why the org (and we) stay on Rocq 9.1.1 rather than 9.2.
7. `ROCQ_WORKSPACE` constrains all paths; rely on `_CoqProject` auto-detection or use an in-repo gitignored `scratch/`.
8. Stale-state hazards: sessions read `.v` at `rocq_start`; edits → `stale_warning`; external `make` unobserved. One worktree per concurrent agent.
9. pet RAM: mathcomp/analysis imports are heavy; set `ROCQ_MAX_PET_RSS_MB` per pool member; watch `rocq_diag`.
10. Axiom whitelists disagree (rocq-skills' `check_axioms.sh` lacks `constructive_indefinite_description`); prefer `rocq_verify` / mathcomp-skills' `print-assumptions-check.sh`.
11. mathcomp-skills README is stale (nested `skills/mathcomp-skills/SKILL.md`); `file:line` citations drift ~10 %/year, lemma names are reliable.
12. The rocq plugin's PreToolUse hook blocks `git push`/`--amend`/`gh pr create` wherever `.v` files exist (user-level install ⇒ everywhere). `ROCQ_GUARDRAILS_BYPASS=1 git push` or set `ROCQ_GUARDRAILS_COLLAB_POLICY=allow`.
13. New `.claude/agents/*.md` are not selectable until restart.
14. `rocq_verify` checks the proof proves the *given* statement, not that the statement is right; skeletons need human review against the Lean source.
