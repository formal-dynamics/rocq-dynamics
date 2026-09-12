# Design: porting leanamycs to Rocq/MathComp

Status: v0 (2026-09-10), written before the first line of mathematics. Decisions are
numbered so `docs/PLAN.md` and commit messages can refer to them; revise here, not in
chat logs.

## 1. What is being ported

`reference/leanamycs/` holds two independent Lake packages:

| Lean project | Lines | Blueprint statements | Main theorem |
|---|---:|---:|---|
| `rumor_spread/` (`RumorPush`) | 1,147 | 27 | `push_informs_all_whp`: for `n >= 2`, after `T = (⌈117 ln n⌉ + 23) + ⌈6 ln n⌉` rounds, `Pr[some node uninformed] <= 2/n` |
| `3-majority/` (`ThreeMajority`) | 1,875 | 37 | `majority3_consensus_whp`: if `log n >= 30` and `|I₀| >= (3/5) n`, after `10 + (⌈6 log n⌉ + 2)` rounds `Pr[no consensus] <= 500/n` |

Shared structure (Lean file → role):

- `Prob.lean` — `avg f = (∑ a, f a) / card α`; `expList α T F` = expectation of a
  trajectory functional over `T` i.i.d. uniform rounds, by recursion on `T`; in
  3-majority also `avg_mul_prod`, `avg_prod_pi` (independence over a product space).
- `Model.lean` — round configuration type, `step`, `run` (fold over a list of rounds),
  monotonicity (`subset_step` / `step_mono`).
- `OneRound.lean` — the one *computed* probability per model.
- `Growth.lean`, `Saturation.lean` — the two phases; `Main.lean` — numerics + glue.
- `Bounds.lean` — elementary real inequalities (Bernoulli, `1 - 1/x <= log x`, …).
- `Chernoff.lean` (3-majority only) — MGF bound and tail bounds from `1 + x <= exp x`.

## 2. Decisions

**D1. Library stack.** MathComp 2.5 + mathcomp-analysis 1.16 for `R : realType`, `expR`,
`ln` (`mathcomp.analysis.exp`) and `boolp` classical logic. No infotheo (unused in the
LLM4Rocq org), no measure theory, no `probability T R`. Rationale: the Lean design
deliberately avoids measure theory; keeping the port equally elementary keeps the
proof search space small for agents and the axiom budget at the three `boolp` axioms.

**D2. One shared probability layer.** Unlike the Lean monorepo, which duplicates
`Prob.lean` in both packages, Rocq gets a single `theories/prob/` layer used by both
processes (`rumor` and `majority` are parallel leaves of the layering).

**D3. Representations (Lean → Rocq).**

| Lean | Rocq | Notes |
|---|---|---|
| `Fintype α` | `T : finType` | |
| `Finset (Fin n)` | `{set 'I_n}` | `cardsU`, `imsetP`, `inE` |
| `Fin n → β` (a round) | `{ffun 'I_n -> B}` | finType when `B` is; `ffunE`, `card_ffun` |
| `Tgt n := ∀ v : Fin n, {u // u ≠ v}` | `{dffun forall v : 'I_n, {u : 'I_n \| u != v}}` (dependent finfun, a `finType`; `Notation Tgt n`) | decided 2026-09-12: exactly Lean's type; `card_dep_ffun`/`card_sig` give `#|Tgt n| = (n-1)^n` |
| `Tgt3 n := Fin n → Fin n × Fin n × Fin n` | `{ffun 'I_n -> 'I_n * 'I_n * 'I_n}` | |
| `step I r = I ∪ I.image r` | `I :|: [set r v \| v in I]` | |
| `run I l` (`List` fold) | `foldl (fun I r => step I r) I s` on `seq` | keep `run_cat` = `run_append` |
| `avg f = (∑ a, f a) / card α` | `avg f := (\sum_(a : T) f a) / #|T|%:R` | `0/0 = 0` convention holds in MathComp too |
| `expList α T F` by recursion | `Fixpoint expList (k : nat) (F : seq T -> R)` | `avg (fun a => expList k (fun s => F (a :: s)))` |
| `Real.exp`, `Real.log` | `expR` (module `sequences`), `ln` (module `exp`) | `expR_ge1Dx` is Lean's `add_one_le_exp`; `exp` does not re-export `sequences`, so the prelude imports both |
| `⌈x⌉₊` (`Nat.ceil`) | `Num.ceil x` (`int`) coerced, or `` `|Num.ceil x| `` | state the main theorems with the same rounding as Lean |
| `∏ i, f i` over `Fin n` | `\prod_(i < n) f i` | `big_ord_recl`, `prodr_ge0` |
| `Finset.sum_boole`, `avg_indicator` | `sumr_const`, `big_mkcond`, `card` lemmas | |
| `positivity`, `linarith`, `nlinarith`, `norm_num` | `lra`, `nra`, `ring`, `field` (algebra-tactics) + explicit `ler_*` lemmas | numerics in `Main` are the risky part |
| `omega` | `lia`/`nia` via zify | |

**D4. Statement fidelity.** Every Rocq theorem that has a Lean counterpart carries the
Lean name in its docstring and states the *same* constants. Any change of constants
(even an improvement) is a separate, documented step after the faithful port compiles.

**D5. Statement-first, then proofs.** Port all definitions and theorem statements of a
module as `Admitted` skeletons, compile with `rocq_compile_file mode="vos"`, review
against the Lean source, then fill proofs (interactively via rocq-mcp or with
`/rocq:autoprove`). `rocq_verify` against the frozen skeleton guards against silently
weakened statements.

**D6. Layering** `prelude < prob < rumor | majority`, enforced by
`scripts/check_layers.py`. File map in `docs/PLAN.md`.

**D7. Axiom budget.** Only the three `boolp` axioms (automatically pulled in by
mathcomp-analysis). `verify.sh` audits the headline theorems; CI runs it.

**D8. Blueprint.** A `rocqblueprint` site (`\rocq{Dynamics.<module>.<name>}` tags)
mirroring the two Lean blueprints statement-for-statement, so progress is visible to
the mathematician co-authors; generated later by `rocqblueprint new`. The LaTeX
papers in `reference/leanamycs/*/latex/` remain the informal proofs.

**D9. Agents.** All agent tooling is user-level (rocq-mcp, rocqet, `rocq` and
`mathcomp-skills` plugins, opam switch `rocq-9.1.1`), so this repo carries only
`CLAUDE.md`, the gates, and (later) a `.claude/agents/` pool for parallel provers.

## 3. Open questions

- Whether to keep Lean's `expList` or state everything over the product space
  `{ffun 'I_T -> Tgt n}` directly (Lean proves both agree in `Equivalence.lean`).
  Start with `expList` (conditioning is definitional), port `Equivalence` last.
- `Num.ceil` returns `int`; `ceiln x := `|Num.ceil x|` (currently in `rumor/main.v`) is Lean's
  `Nat.ceil` for `x >= 0`; move it to the prelude once the prelude is next rebuilt.
- The prelude exports `classical_sets`, whose `set0`/`setT`/`set1` shadow finset's; the rumor
  files write `finset.set0` for now. Drop `classical_sets` from the prelude exports at the next
  prelude rebuild (only `boolp`, `reals`, `sequences`, `exp` are needed).

## 4. Lessons from the first proofs (keep adding)

- The prelude must `Require Export` (not `Import`) the libraries, and `Export` the
  theory modules, otherwise downstream files do not even see `realType`.
- In `ring_scope`, `nat` comparisons need `%N` (`(n <= m)%N`), and a boolean
  indicator under `%:R` must be scoped: `((k <= x)%R)%:R`, because the argument of
  `%:R` is parsed in `nat_scope`.
- `rewrite foo` picks the first matching subterm; use `[in RHS]foo`,
  `[in X in X / _]foo` or `-[c *+ _]foo` to aim (bit us in `avg_ind`, `avg_const`).
- `case: (P a)` does not see `P a` hidden inside `[pred a | P a] a`; `rewrite inE`
  (or `/=`) first.
- Rewriting with a higher-order pattern only works when the metavariable is applied
  to bound variables: `pair_bigA` must be used left-to-right after `big_distrlr`,
  `rewrite -pair_bigA` fails.
- Lean's hand-rolled `avg_prod_pi` is MathComp's `bigA_distr_bigA` plus
  `card_ffun`, `natrX`, `prodr_const`, `exprVn`.
- Empty sample spaces: MathComp's `x / 0 = 0` gives the same `avg = 0` convention
  as Lean; nonemptiness is the hypothesis `(0 < #|T|)%N`.
- A comparison whose two sides are both casts (`n%:R <= #|I|%:R`, `1 <= n%:R - ...`,
  `500 * ln n%:R <= n%:R / 4`) has no anchor for the ring: write `... :> R`.
- A `nat`-valued definition that depends on `R` only through `ln` (`T2a`) gets an
  uninferable implicit `R` under `Set Implicit Arguments`; `Arguments T2a : clear implicits`.
- `rewrite avg_prod_ffun` cannot infer `f` from `expR (t * Y i (x i))` (metavariable applied
  to `x i`); instantiate it: `rewrite -(avg_prod_ffun (fun i y => expR (t * Y i y)))`,
  then `congr avg; apply/funext`. Same for replacing a lambda under `avg`.
- `case: (leP k (X x))` with explicit arguments (otherwise `leP` grabs the goal's outer
  `<=`); `-[leLHS]expR0 ler_expR` then `nra` proves `1 <= expR (...)`.
- `lra`/`nra` treat `expR t`, `ln x`, `m^-1` as atoms; they close most real side goals
  once the transcendental facts are in the context.
- MathComp has no Bernoulli inequality and no `sum_le_exp_of_nonneg`; `bounds.v` proves
  `one_sub_mul_le_pow` by induction (`nra` steps; the regime `1 < x <= 2` via `normrX`,
  `exprn_ile1`, `ler_norml`) and adds `expR_ge_series`/`expR_ge_taylor2` from
  `nondecreasing_cvgn_le`, `nondecreasing_series`, `is_cvg_series_exp_coeff`.
- `lra`/`nra` treat `k`!%:R` as opaque; convert factorials to numerals first
  (`rewrite (_ : 3`!%:R = 6 :> R) //`). `rewrite exprS` picks the first `_ ^+ _.+1`; aim it
  with `[(1 - x) ^+ _]exprS`.
- Mathlib ↔ MathComp-Analysis dictionary for logs: `log_le_sub_one_of_pos` ↔ `le_ln1Dx`,
  `log_inv` ↔ `lnV ?posrE`, `log_div` ↔ `ln_div ?posrE`, `log_exp` ↔ `expRK`,
  `exp_neg` ↔ `expRN`, `log_le_log` ↔ `ler_ln ?posrE`, `exp_nat_mul` ↔ `expRM_natl`,
  `exp_one_gt_d9` ↔ `expR_ge_series 6` (gives `163/60 <= expR 1`); `ln 0 = 0` is `ln0`.
