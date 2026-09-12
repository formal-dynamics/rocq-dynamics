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
| `Tgt n := ∀ v : Fin n, {u // u ≠ v}` | `{ffun 'I_n -> 'I_n}` restricted by `[forall v, f v != v]`, packaged as a `subFinType` (or `{ffun 'I_n -> 'I_n.-1}` composed with `lift`) | pick whichever makes `card_tgt : #|Tgt n| = (n-1)^n` and `avg_not_contacted` easiest |
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

- `Tgt n` representation (D3): subtype of `{ffun 'I_n -> 'I_n}` vs `{ffun 'I_n -> 'I_n.-1}`
  with `lift v`. Decide when porting `OneRound.card_tgt`.
- Whether to keep Lean's `expList` or state everything over the product space
  `{ffun 'I_T -> Tgt n}` directly (Lean proves both agree in `Equivalence.lean`).
  Start with `expList` (conditioning is definitional), port `Equivalence` last.
- `Num.ceil` returns `int`; the cleanest way to state `⌈117 ln n⌉ + 23` as a `nat`.
