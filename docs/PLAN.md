# Plan and status

Milestones for the Rocq port of `reference/leanamycs/`. Update the status table in
every checkpoint commit that changes it. Decisions referenced as D1… are in
`docs/DESIGN.md`.

## Milestones

| # | Milestone | Done when |
|---|---|---|
| M0 | Toolchain + repo skeleton | `make gate` green on `theories/prelude.v`; CI green; tooling documented in `docs/study/` |
| M1 | Probability layer, statements | `theories/prob/{avg,indep,bounds,chernoff}.v` compile with `Admitted` skeletons for every Lean declaration of `Prob.lean`, `Bounds.lean`, `Chernoff.lean` (both projects, deduplicated) |
| M2 | Probability layer, proofs | M1 files `Admitted`-free; `verify.sh` audits `avg_exp_le`, `avg_tail_ge_log`, `avg_tail_le_log` |
| M3 | Rumor spreading, statements | `theories/rumor/{model,oneround,growth,saturation,main}.v` skeletons compile; statements reviewed against Lean |
| M4 | Rumor spreading, proofs | `push_informs_all_whp` proved, audited |
| M5 | 3-majority, statements | `theories/majority/{model,oneround,growth,saturation,main}.v` skeletons compile |
| M6 | 3-majority, proofs | `majority3_consensus_whp` proved, audited |
| M7 | Blueprint + Pages | `rocqblueprint` site mirroring both Lean blueprints, deployed; coqdoc |
| M8 | Faithfulness audit | `docs/LEAN_TO_ROCQ.md` maps every Lean declaration to its Rocq counterpart; `Equivalence.lean` ported |

## File map (Lean → Rocq)

| Lean | Rocq | Layer |
|---|---|---|
| `RumorSpread/Prob.lean`, `ThreeMajority/Prob.lean` (avg, expList) | `theories/prob/avg.v` | prob |
| `ThreeMajority/Prob.lean` (`avg_mul_prod`, `avg_prod_pi`, `avg_eval`) | `theories/prob/indep.v` | prob |
| `RumorSpread/Bounds.lean`, `ThreeMajority/Bounds.lean` | `theories/prob/bounds.v` | prob |
| `ThreeMajority/Chernoff.lean` | `theories/prob/chernoff.v` | prob |
| `RumorSpread/Model.lean` | `theories/rumor/model.v` | rumor |
| `RumorSpread/OneRound.lean` | `theories/rumor/oneround.v` | rumor |
| `RumorSpread/Growth.lean` | `theories/rumor/growth.v` | rumor |
| `RumorSpread/Saturation.lean` | `theories/rumor/saturation.v` | rumor |
| `RumorSpread/Main.lean` | `theories/rumor/main.v` | rumor |
| `RumorSpread/Equivalence.lean` | `theories/prob/equivalence.v` | prob (M8) |
| `ThreeMajority/Model.lean` | `theories/majority/model.v` | majority |
| `ThreeMajority/OneRound.lean` | `theories/majority/oneround.v` | majority |
| `ThreeMajority/Growth.lean` | `theories/majority/growth.v` | majority |
| `ThreeMajority/Saturation.lean` | `theories/majority/saturation.v` | majority |
| `ThreeMajority/Main.lean` | `theories/majority/main.v` | majority |

## Status

| File | Statements ported | Admitted remaining | Notes |
|---|---:|---:|---|
| `theories/prelude.v` | – | 0 | smoke lemmas; `make gate` and `verify.sh` green (M0 done 2026-09-11) |
| `theories/prob/avg.v` | 19/19 | 0 | proved 2026-09-12 |
| `theories/prob/indep.v` | 6/6 | 0 | proved 2026-09-12; `bigA_distr_bigA` replaces Lean's hand induction |
| `theories/prob/bounds.v` | 12/12 (+2 helpers) | 0 | proved 2026-09-12 (agent); M2 complete |
| `theories/prob/chernoff.v` | 7/7 | 0 | proved 2026-09-12 (agent, 3 compile iterations) |
| `theories/rumor/model.v` | 16/16 | 15 | skeletons compile 2026-09-12; `Tgt n` is a dependent finfun |
| `theories/rumor/oneround.v` | 7/7 | 7 | skeletons compile |
| `theories/rumor/growth.v` | 3/3 | 0 | proved 2026-09-12 (agent) |
| `theories/rumor/saturation.v` | 1/1 | 0 | proved 2026-09-12 (agent) |
| `theories/rumor/main.v` | 7/7 | 6 | skeletons compile; `ceiln` = Lean `Nat.ceil` (move to prelude later) |
| `theories/majority/model.v` | 13/13 | 10 | skeletons compile 2026-09-12 |
| `theories/majority/oneround.v` | 18/18 | 0 | proved 2026-09-12 (agent) |
| `theories/majority/growth.v` | 10/10 | 9 | skeletons compile |
| `theories/majority/saturation.v` | 17/17 | 14 | skeletons compile; `T2a n R` takes `R` explicitly |
| `theories/majority/main.v` | 7/7 | 7 | skeletons compile |

## Working agreements

- One branch (or one git worktree + one rocq-mcp pool member) per file when running
  agents in parallel; merge through PRs so CI's `make gate` runs.
- A file enters the status table when its skeleton compiles; it leaves "Admitted
  remaining > 0" only when `verify.sh` lists its headline lemma.
- Constants are frozen at the Lean values (D4). Improvements go to a `sharper/`
  branch after the faithful port is complete.
