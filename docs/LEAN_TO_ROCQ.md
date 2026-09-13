# Lean → Rocq faithfulness audit

Status: v1 (2026-09-13, milestone M8). Every `def`/`lemma`/`theorem`/`instance` of
`reference/leanamycs/rumor_spread/RumorSpread/*.lean` and
`reference/leanamycs/3-majority/ThreeMajority/*.lean` is listed once, with its
Rocq counterpart in `theories/`, and the *statement* differences between the two.
Statements were compared by reading both sources side by side (Lean statement vs
the Rocq `Lemma`/`Theorem` header); the docstrings `(** Lean: [name] ... *)` in
the Rocq files give the intended mapping, this document checks it.

Summary of the audit: **no hypothesis is strengthened or weakened, no constant is
changed, and no quantifier order differs** in any of the 169 mapped declarations
(176 Lean declarations in total; the 7 unmapped ones are 5 typeclass instances that
MathComp derives automatically and 2 private proof devices).
Every difference is one of the representation changes catalogued in §1, each of
which is a provable equivalence of the two statements. Rocq-only helpers are in
§4, proof-level deviations (which do not affect statements) in §5, and the
verdict on the two headline theorems in §6.

## 1. Dictionary of representation changes

Tags used in the "statement differences" columns below. Each tag denotes a change
of representation under which the Lean and Rocq statements are equivalent; the
justification is given once here.

| Tag | Lean | Rocq | Why equivalent |
|---|---|---|---|
| **[R]** | `ℝ` | `R : realType` (mathcomp-analysis; `Context {R : realType}`) | Every statement is proved for an arbitrary real closed ordered field with `expR`/`ln`; `ℝ` is an instance. |
| **[F]** | `Finset (Fin n)`, `I.card`, `∈`, `⊆`, `univ`, `{v₀}`, `Iᶜ`, `I.Nonempty`, `Fin n` | `{set 'I_n}`, `#\|I\|`, `\in`, `\subset`, `[set: 'I_n]`, `[set v0]`, `~: I`, `I != set0`, `'I_n` | `{set 'I_n}` is the finite type of subsets of `'I_n`; `Fin n ≃ 'I_n`. |
| **[L]** | `List α`, `[]`, `::`, `++`, `List.ofFn ω` | `seq T`, `[::]`, `::`, `++`, `tval w` (`w : k.-tuple T`) | Same inductive type. |
| **[I]** | `if P then (1:ℝ) else 0` for decidable `P` | `(P)%:R` (a `bool` coerced to `nat` then to `R`), e.g. `((k <= X x)%R)%:R`; `if P then 0 else 1` becomes the indicator of the negation, written `(P == false)%:R`, `(u \notin S)%:R` or `(A != B)%:R` | `nat_of_bool true = 1`, `nat_of_bool false = 0`. |
| **[B]** | `Prop` with `Decidable` instance, `↔`, `≠`, `∨` | `bool`, `=` on `bool` or `reflect`, `!=`, `\|\|` | Decidable propositions are booleans; `reflect P b` / `(P) = (Q)` on `bool` is `↔`. |
| **[E]** | `∃ v ∈ I, P v`; `∀ v ∈ I, P v` | `exists2 v, v \in I & P v`; `[forall v in I, P v]` (bool) | Bounded quantifiers over a finite set. |
| **[N]** | `[Nonempty α]` (instance) | `(0 < #\|T\|)%N` (premise) | A finite type is nonempty iff its cardinality is positive. |
| **[C]** | `⌈x⌉₊` (`Nat.ceil x`) | ``ceiln x := `\|Num.ceil x\|`` (`theories/prelude.v`) | Equal whenever `x >= 0`. Every occurrence is `x = c * ln n%:R` with `c ∈ {6, 9, 117}`, and `ln n%:R >= 0` for **every** `n : nat` (`ln 0 = ln 1 = 0` in both libraries: `ln0`, `ln1`; `Real.log_zero`, `Real.log_one`), so the two functions agree on all arguments that occur, without any side hypothesis. |
| **[Nat]** | `(n : ℝ)`, `(I.card : ℝ)`, `x ^ k`, `Real.exp`, `Real.log`, `k.factorial`, `max` | `n%:R`, `#\|I\|%:R`, `x ^+ k`, `expR`, `ln`, ``k`!``, `Num.max` | Same functions; `nat` (in)equalities carry `%N`. |
| **[S]** | Explicit arguments `(n : ℕ)`, `(Y) (hY)`, `(α) [Fintype α]` | Section `Variable n : nat`, `Variable Y`, `Hypothesis Y01`, `Implicit Types`; `R`, `T` implicit (`Arguments avg {R T} f`, `Arguments expList {R T} k F`) | Section variables are abstracted at `End`; Lean's `expList α T F` has `α` explicit, Rocq's `expList k F` infers `T` from `F`. |
| **[Q]** | Hypotheses as named binders before the colon, e.g. `(hn : 2 ≤ n)` | The same hypotheses as premises after the colon, `(2 <= n)%N -> ...`, in the same order | Curried implication; universally quantified variables keep their order. |
| **[G]** | `Finset` sums `∑ i ∈ s, f i` | `\sum_(i <- r \| P i) f i` over a `seq` with a filter | The Rocq statement is a *generalisation*: `s` is the instance `r := enum s`, `P := predT`. Only `avg_sum` is affected. |
| **[Eq]** | `e : α ≃ β` (an `Equiv`) | `e : T -> U` with `bijective e` | `bijective e := exists g, cancel e g /\ cancel g e` is exactly the data of an `Equiv`; Mathlib's `Equiv.ofBijective` and `Equiv.bijective` translate the two forms. Only `avg_equiv`/`avg_bij` is affected. |

Constants are listed per row and are identical on both sides in every case.

## 2. `rumor_spread/RumorSpread/*.lean` (Lean namespace `RumorPush`)

### 2.1 `Prob.lean` → `theories/prob/avg.v`

| Lean name | Rocq file | Rocq name | Statement differences |
|---|---|---|---|
| `avg (f : α → ℝ) : ℝ := (∑ a, f a) / (Fintype.card α : ℝ)` | prob/avg.v | `avg {T} (f : T -> R) : R := (\sum_(a : T) f a) / #\|T\|%:R` | [R][S]. Same `0/0 = 0` convention on empty types. |
| `avg_nonneg (hf : ∀ a, 0 ≤ f a) : 0 ≤ avg f` | prob/avg.v | `avg_ge0 : (forall a, 0 <= f a) -> 0 <= avg f` | [Q]. |
| `avg_le_avg (h : ∀ a, f a ≤ g a) : avg f ≤ avg g` | prob/avg.v | `avg_le : (forall a, f a <= g a) -> avg f <= avg g` | [Q]. |
| `avg_add f g : avg (fun a => f a + g a) = avg f + avg g` | prob/avg.v | `avgD` | none. |
| `avg_sub f g : avg (fun a => f a - g a) = avg f - avg g` | prob/avg.v | `avgB` | none. |
| `avg_const_mul c f : avg (fun a => c * f a) = c * avg f` | prob/avg.v | `avgZ` | none. |
| `avg_sum (s : Finset ι) (f : ι → α → ℝ) : avg (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, avg (f i)` | prob/avg.v | `avg_sum (r : seq I) (P : pred I) f : avg (fun a => \sum_(i <- r \| P i) f i a) = \sum_(i <- r \| P i) avg (f i)` | [G] (Rocq strictly more general). |
| `avg_indicator (P : α → Prop) [DecidablePred P] : avg (fun a => if P a then 1 else 0) = ((univ.filter P).card : ℝ) / card α` | prob/avg.v | `avg_ind (P : pred T) : avg (fun a => (P a)%:R : R) = #\|[pred a \| P a]\|%:R / #\|T\|%:R` | [I][B]: `univ.filter P` → `[pred a \| P a]`. |
| `card_cast_pos [Nonempty α] : (0 : ℝ) < card α` | prob/avg.v | `card_gt0R : (0 < #\|T\|)%N -> (0 : R) < #\|T\|%:R` | [N]. |
| `avg_const [Nonempty α] c : avg (fun _ => c) = c` | prob/avg.v | `avg_const c : (0 < #\|T\|)%N -> avg (fun _ : T => c) = c` | [N]. |
| `expList α : ℕ → (List α → ℝ) → ℝ` (by recursion: `0, F => F []`; `T+1, F => avg fun a => expList α T fun l => F (a :: l)`) | prob/avg.v | `Fixpoint expList {T} (k : nat) (F : seq T -> R) : R` (same two clauses) | [L][S]. |
| `expList_zero F : expList α 0 F = F []` | prob/avg.v | `expList0 : expList 0 F = F [::]` | [L]. |
| `expList_succ T F : expList α (T+1) F = avg fun a => expList α T fun l => F (a :: l)` | prob/avg.v | `expListS : expList k.+1 F = avg (fun a => expList k (fun s => F (a :: s)))` | [L]. |
| `expList_nonneg (h : ∀ l, 0 ≤ F l) : 0 ≤ expList α T F` | prob/avg.v | `expList_ge0 : (forall s, 0 <= F s) -> 0 <= expList k F` | [Q]. |
| `expList_le_expList (h : ∀ l, F l ≤ G l) : expList α T F ≤ expList α T G` | prob/avg.v | `expList_le : (forall s, F s <= G s) -> expList k F <= expList k G` | [Q]; `k` is an explicit argument in Rocq. |
| `expList_add T F G : expList α T (fun l => F l + G l) = expList α T F + expList α T G` | prob/avg.v | `expListD` | none. |
| `expList_const_mul T c F : expList α T (fun l => c * F l) = c * expList α T F` | prob/avg.v | `expListZ` | none. |
| `expList_const [Nonempty α] T c : expList α T (fun _ => c) = c` | prob/avg.v | `expList_const : (0 < #\|T\|)%N -> expList k (fun _ => c) = c` | [N]. |
| `expList_append T₁ T₂ F : expList α (T₁ + T₂) F = expList α T₁ fun l₁ => expList α T₂ fun l₂ => F (l₁ ++ l₂)` | prob/avg.v | `expList_cat : expList (k1 + k2) F = expList k1 (fun s1 => expList k2 (fun s2 => F (s1 ++ s2)))` | [L]. |

### 2.2 `Model.lean` → `theories/rumor/model.v`

| Lean name | Rocq file | Rocq name | Statement differences |
|---|---|---|---|
| `def Tgt (n : ℕ) := ∀ v : Fin n, {u : Fin n // u ≠ v}` | rumor/model.v | `Notation Tgt n := {dffun forall v : 'I_n, {u : 'I_n \| u != v}}` | [F][B]: dependent function into a subtype, as in Lean; `u ≠ v` → `u != v`. |
| `instance (n) : Fintype (Tgt n)` | — | — | Automatic: a dependent finfun over a `finType` with `finType` fibres is a `finType` (MathComp `finfun`/`{dffun ...}` instances). |
| `instance (n) : DecidableEq (Tgt n)` | — | — | Automatic: every `finType` is an `eqType`. |
| `tgt_nonempty (hn : 2 ≤ n) : Nonempty (Tgt n)` | rumor/model.v | `tgt_gt0 : (2 <= n)%N -> (0 < #\|Tgt n\|)%N` | [N][Q]. Constant `2`. |
| `step I r := I ∪ I.image fun v => ((r v) : Fin n)` | rumor/model.v | `step I r := I :\|: [set val (r v) \| v in I]` | [F]. |
| `subset_step I r : I ⊆ step I r` | rumor/model.v | `subset_step : I \subset step I r` | [F]. |
| `card_le_card_step I r : I.card ≤ (step I r).card` | rumor/model.v | `card_le_card_step : (#\|I\| <= #\|step I r\|)%N` | [F]. |
| `card_step_le I r : (step I r).card ≤ 2 * I.card` | rumor/model.v | `card_step_le : (#\|step I r\| <= 2 * #\|I\|)%N` | [F]. Constant `2`. |
| `mem_step : u ∈ step I r ↔ u ∈ I ∨ ∃ v ∈ I, ((r v) : Fin n) = u` | rumor/model.v | `mem_step : reflect (u \in I \/ exists2 v, v \in I & val (r v) = u) (u \in step I r)` | [B][E]. |
| `run I : List (Tgt n) → Finset (Fin n)` (`[] => I`; `r :: l => run (step I r) l`) | rumor/model.v | `Fixpoint run I s := if s is r :: s' then run (step I r) s' else I` | [L]; same recursion. |
| `run_nil I : run I [] = I` | rumor/model.v | `run_nil` | [L]. |
| `run_cons I r l : run I (r :: l) = run (step I r) l` | rumor/model.v | `run_cons` | [L]. |
| `subset_run I l : I ⊆ run I l` | rumor/model.v | `subset_run : I \subset run I s` | [F]. |
| `run_append I l₁ l₂ : run I (l₁ ++ l₂) = run (run I l₁) l₂` | rumor/model.v | `run_cat` | [L]. |
| `card_run_le I l : (run I l).card ≤ n` | rumor/model.v | `card_run_le : (#\|run I s\| <= n)%N` | [F]. |
| `goodRound I r : Prop := 9 * I.card ≤ 8 * (step I r).card ∨ n < 2 * I.card` | rumor/model.v | `goodRound I r : bool := (9 * #\|I\| <= 8 * #\|step I r\|)%N \|\| (n < 2 * #\|I\|)%N` | [B]. Constants `9, 8, 2`. |
| `instance : Decidable (goodRound I r)` | — | — | `goodRound` is a `bool`. |
| `goodCount I : List (Tgt n) → ℕ` (`r :: l => (if goodRound I r then 1 else 0) + goodCount (step I r) l`) | rumor/model.v | `Fixpoint goodCount I s := if s is r :: s' then goodRound I r + goodCount (step I r) s' else 0` | [L][I] (`bool` coerced to `nat`). |
| `goodCount_nil I : goodCount I [] = 0` | rumor/model.v | `goodCount_nil` | [L]. |
| `goodCount_cons I r l : goodCount I (r :: l) = (if goodRound I r then 1 else 0) + goodCount (step I r) l` | rumor/model.v | `goodCount_cons : goodCount I (r :: s) = (goodRound I r + goodCount (step I r) s)%N` | [L][I]. |
| `pow_goodCount_mul_card_le_card_run I l (h : 2 * (run I l).card ≤ n) : ((9:ℝ)/8) ^ goodCount I l * I.card ≤ ((run I l).card : ℝ)` | rumor/model.v | `pow_goodCount_mul_card_le_card_run (R : realType) I s : (2 * #\|run I s\| <= n)%N -> (9 / 8 : R) ^+ goodCount I s * #\|I\|%:R <= #\|run I s\|%:R` | [R][F][Q]; `R` explicit. Constants `9/8, 2`. |

### 2.3 `OneRound.lean` → `theories/rumor/oneround.v`

| Lean name | Rocq file | Rocq name | Statement differences |
|---|---|---|---|
| `card_tgt n : Fintype.card (Tgt n) = (n - 1) ^ n` | rumor/oneround.v | `card_tgt n : #\|Tgt n\| = ((n - 1) ^ n)%N` | [Nat]; truncated `nat` subtraction on both sides. |
| `private def notContactedEquiv I u : {r : Tgt n // ∀ v ∈ I, (r v : Fin n) ≠ u} ≃ ∀ v, {x // x ≠ v ∧ (v ∈ I → x ≠ u)}` | — | — | Proof device only; the Rocq proof of `card_not_contacted` counts the same set directly as a `family F` via `card_family` (no explicit equivalence needed). |
| `card_subtype_ne_ne (hvu : v ≠ u) : card {x : Fin n // x ≠ v ∧ x ≠ u} = n - 2` | rumor/oneround.v | `card_sig_ne_ne v u : v != u -> #\|{: {x : 'I_n \| (x != v) && (x != u)}}\| = (n - 2)%N` | [B][Q]. Constant `2`. |
| `card_filter_not_contacted I u (hu : u ∉ I) : (univ.filter fun r : Tgt n => ∀ v ∈ I, (r v : Fin n) ≠ u).card = (n - 2) ^ I.card * (n - 1) ^ (n - I.card)` | rumor/oneround.v | `card_not_contacted I u : u \notin I -> #\|[set r : Tgt n \| [forall v in I, val (r v) != u]]\| = ((n - 2) ^ #\|I\| * (n - 1) ^ (n - #\|I\|))%N` | [F][E][Q]. |
| `avg_not_contacted (hn : 2 ≤ n) I u (hu : u ∉ I) : avg (fun r => if u ∈ step I r then (0:ℝ) else 1) = (1 - 1 / ((n:ℝ) - 1)) ^ I.card` | rumor/oneround.v | `avg_not_contacted I u : (2 <= n)%N -> u \notin I -> avg (fun r : Tgt n => (u \notin step I r)%:R : R) = (1 - 1 / (n%:R - 1)) ^+ #\|I\|` | [I] (indicator of `u ∉ step I r`), [F][Q]. Constants `2, 1`. |
| `avg_card_step (hn : 2 ≤ n) I : avg (fun r => ((step I r).card : ℝ)) = I.card + ((n:ℝ) - I.card) * (1 - (1 - 1/((n:ℝ)-1)) ^ I.card)` | rumor/oneround.v | `avg_card_step I : (2 <= n)%N -> avg (fun r => #\|step I r\|%:R : R) = #\|I\|%:R + (n%:R - #\|I\|%:R) * (1 - (1 - 1 / (n%:R - 1)) ^+ #\|I\|)` | [F][Q]. |
| `prob_goodRound (hn : 2 ≤ n) I (hI : I.Nonempty) : (1:ℝ)/8 ≤ avg (fun r => if goodRound I r then 1 else 0)` | rumor/oneround.v | `prob_goodRound I : (2 <= n)%N -> I != set0 -> 1 / 8 <= avg (fun r => (goodRound I r)%:R : R)` | [F][I][Q]. Constant `1/8`. |
| `avg_uninformed_le (hn : 2 ≤ n) I (hhalf : n ≤ 2 * I.card) : avg (fun r => (n:ℝ) - (step I r).card) ≤ 2/3 * ((n:ℝ) - I.card)` | rumor/oneround.v | `avg_uninformed_le I : (2 <= n)%N -> (n <= 2 * #\|I\|)%N -> avg (fun r => n%:R - #\|step I r\|%:R : R) <= 2 / 3 * (n%:R - #\|I\|%:R)` | [F][Q]. Constants `2, 2/3`. |

### 2.4 `Growth.lean` → `theories/rumor/growth.v`

| Lean name | Rocq file | Rocq name | Statement differences |
|---|---|---|---|
| `avg_half_pow_good (hn : 2 ≤ n) I (hI : I.Nonempty) : avg (fun r => ((1:ℝ)/2) ^ (if goodRound I r then 1 else 0)) ≤ 15/16` | rumor/growth.v | `avg_half_pow_good I : (2 <= n)%N -> I != set0 -> avg (fun r => (1 / 2 : R) ^+ goodRound I r) <= 15 / 16` | [F][I] (exponent is the `bool` coerced to `nat`), [Q]. Constants `1/2, 15/16`. |
| `expList_half_pow_goodCount (hn : 2 ≤ n) (T : ℕ) : ∀ I, I.Nonempty → expList (Tgt n) T (fun l => ((1:ℝ)/2) ^ goodCount I l) ≤ ((15:ℝ)/16) ^ T` | rumor/growth.v | `expList_half_pow_goodCount k : (2 <= n)%N -> forall I, I != set0 -> expList k (fun s => (1 / 2 : R) ^+ goodCount I s) <= (15 / 16) ^+ k` | [F][Q]; `∀ I` after `T`/`k` in both. Constants `1/2, 15/16`. |
| `phase1 (hn : 2 ≤ n) v₀ (L T₁ : ℕ) (hL : (n:ℝ) ≤ ((9:ℝ)/8) ^ L) : expList (Tgt n) T₁ (fun l => if 2 * (run {v₀} l).card ≤ n then 1 else 0) ≤ 2 ^ L * ((15:ℝ)/16) ^ T₁` | rumor/growth.v | `phase1 v0 (L k1 : nat) : (2 <= n)%N -> n%:R <= (9 / 8 : R) ^+ L -> expList k1 (fun s => ((2 * #\|run [set v0] s\| <= n)%N)%:R : R) <= 2 ^+ L * (15 / 16) ^+ k1` | [F][I][Q]. Constants `9/8, 2, 15/16`. |

### 2.5 `Saturation.lean` → `theories/rumor/saturation.v`

| Lean name | Rocq file | Rocq name | Statement differences |
|---|---|---|---|
| `saturation (hn : 2 ≤ n) (T : ℕ) : ∀ I, n ≤ 2 * I.card → expList (Tgt n) T (fun l => (n:ℝ) - (run I l).card) ≤ ((2:ℝ)/3) ^ T * ((n:ℝ) - I.card)` | rumor/saturation.v | `saturation k : (2 <= n)%N -> forall I : {set 'I_n}, (n <= 2 * #\|I\|)%N -> expList k (fun s => n%:R - #\|run I s\|%:R : R) <= (2 / 3) ^+ k * (n%:R - #\|I\|%:R)` | [F][Q]. Constants `2, 2/3`. |

### 2.6 `Bounds.lean` → `theories/prob/bounds.v`

| Lean name | Rocq file | Rocq name | Statement differences |
|---|---|---|---|
| `one_sub_mul_le_pow (hx : x ≤ 2) (m : ℕ) : 1 - m * x ≤ (1 - x) ^ m` | prob/bounds.v | `one_sub_mul_le_pow x m : x <= 2 -> 1 - m%:R * x <= (1 - x) ^+ m` | [Q]. Constant `2`. |
| `mul_sub_sq_le_one_sub_pow (hx0 : 0 ≤ x) (hx1 : x ≤ 1) m : m * x - m ^ 2 * x ^ 2 / 2 ≤ 1 - (1 - x) ^ m` | prob/bounds.v | `mul_sub_sq_le_one_sub_pow x m : 0 <= x -> x <= 1 -> m%:R * x - m%:R ^+ 2 * x ^+ 2 / 2 <= 1 - (1 - x) ^+ m` | [Q]. |
| `half_mul_le_one_sub_pow (hx0) (hx1) (hmx : (m:ℝ) * x ≤ 1) : m * x / 2 ≤ 1 - (1 - x) ^ m` | prob/bounds.v | `half_mul_le_one_sub_pow x m : 0 <= x -> x <= 1 -> m%:R * x <= 1 -> m%:R * x / 2 <= 1 - (1 - x) ^+ m` | [Q]. |
| `pow_one_sub_le_one_div (hx0) (hx1) m : (1 - x) ^ m ≤ 1 / (1 + m * x)` | prob/bounds.v | `pow_one_sub_le_one_div x m : 0 <= x -> x <= 1 -> (1 - x) ^+ m <= 1 / (1 + m%:R * x)` | [Q]. |
| `one_sub_inv_le_log (hx : 0 < x) : 1 - 1 / x ≤ Real.log x` | prob/bounds.v | `one_sub_inv_le_ln x : 0 < x -> 1 - 1 / x <= ln x` | [Nat][Q]. |

### 2.7 `Main.lean` → `theories/rumor/main.v`

| Lean name | Rocq file | Rocq name | Statement differences |
|---|---|---|---|
| `prNotAllInformed (n) (v₀ : Fin n) (T : ℕ) : ℝ := expList (Tgt n) T (fun l => if run {v₀} l = univ then (0:ℝ) else 1)` | rumor/main.v | `prNotAllInformed (v0 : 'I_n) (k : nat) : R := expList k (fun s => (run [set v0] s != [set: 'I_n])%:R)` | [F][I] (indicator of `run ≠ univ`), [S]. |
| `prNotAllInformed_le (hn : 2 ≤ n) v₀ (L T₁ T₂ : ℕ) (hL : (n:ℝ) ≤ ((9:ℝ)/8) ^ L) : prNotAllInformed n v₀ (T₁ + T₂) ≤ 2 ^ L * ((15:ℝ)/16) ^ T₁ + ((2:ℝ)/3) ^ T₂ * n` | rumor/main.v | `prNotAllInformed_le v0 (L k1 k2 : nat) : (2 <= n)%N -> n%:R <= (9 / 8 : R) ^+ L -> prNotAllInformed v0 (k1 + k2) <= 2 ^+ L * (15 / 16) ^+ k1 + (2 / 3) ^+ k2 * n%:R` | [Q]. Constants `9/8, 2, 15/16, 2/3`. |
| `private log_ge_198 : (1:ℝ)/9 ≤ Real.log ((9:ℝ)/8)` | rumor/main.v | `ln98_ge : 1 / 9 <= ln (9 / 8 : R)` | [Nat]; public in Rocq. |
| `private log_ge_1615 : (1:ℝ)/16 ≤ Real.log ((16:ℝ)/15)` | rumor/main.v | `ln1615_ge : 1 / 16 <= ln (16 / 15 : R)` | [Nat]; public in Rocq. |
| `private log_ge_32 : (1:ℝ)/3 ≤ Real.log ((3:ℝ)/2)` | rumor/main.v | `ln32_ge : 1 / 3 <= ln (3 / 2 : R)` | [Nat]; public in Rocq. |
| `numeric_A (hn : 2 ≤ n) : (n:ℝ) ≤ ((9:ℝ)/8) ^ (⌈(9:ℝ) * Real.log n⌉₊ + 1)` | rumor/main.v | `numeric_A : (2 <= n)%N -> n%:R <= (9 / 8 : R) ^+ (ceiln (9 * ln (n%:R : R)) + 1)` | [C][Q]. Constants `9/8, 9, 1`. |
| `numeric_B (hn : 2 ≤ n) : 2 ^ (⌈(9:ℝ) * Real.log n⌉₊ + 1) * ((15:ℝ)/16) ^ (⌈(117:ℝ) * Real.log n⌉₊ + 23) ≤ 1 / n` | rumor/main.v | `numeric_B : (2 <= n)%N -> 2 ^+ (ceiln (9 * ln (n%:R : R)) + 1) * (15 / 16 : R) ^+ (ceiln (117 * ln (n%:R : R)) + 23) <= 1 / n%:R` | [C][Q]. Constants `2, 9, 1, 15/16, 117, 23, 1`. |
| `numeric_C (hn : 2 ≤ n) : ((2:ℝ)/3) ^ ⌈(6:ℝ) * Real.log n⌉₊ * n ≤ 1 / n` | rumor/main.v | `numeric_C : (2 <= n)%N -> (2 / 3 : R) ^+ ceiln (6 * ln (n%:R : R)) * n%:R <= 1 / n%:R` | [C][Q]. Constants `2/3, 6, 1`. |
| `theorem push_informs_all_whp (hn : 2 ≤ n) (v₀ : Fin n) : prNotAllInformed n v₀ ((⌈(117:ℝ) * Real.log n⌉₊ + 23) + ⌈(6:ℝ) * Real.log n⌉₊) ≤ 2 / n` | rumor/main.v | `Theorem push_informs_all_whp (v0 : 'I_n) : (2 <= n)%N -> prNotAllInformed v0 ((ceiln (117 * ln (n%:R : R)) + 23) + ceiln (6 * ln (n%:R : R))) <= 2 / n%:R` | [C][F][Q] only. Constants `117, 23, 6, 2`; hypothesis `2 ≤ n`. |
| `theorem push_informs_all_whp' (hn : 2 ≤ n) (v₀) : 1 - 2 / (n:ℝ) ≤ expList (Tgt n) ((⌈(117:ℝ) * Real.log n⌉₊ + 23) + ⌈(6:ℝ) * Real.log n⌉₊) (fun l => if run {v₀} l = univ then (1:ℝ) else 0)` | rumor/main.v | `Theorem push_informs_all_whp' (v0 : 'I_n) : (2 <= n)%N -> 1 - 2 / n%:R <= expList ((ceiln (117 * ln (n%:R : R)) + 23) + ceiln (6 * ln (n%:R : R))) (fun s => (run [set v0] s == [set: 'I_n])%:R : R)` | [C][F][I][Q] only. Same constants and hypothesis. |

### 2.8 `Equivalence.lean` → `theories/prob/equivalence.v`

| Lean name | Rocq file | Rocq name | Statement differences |
|---|---|---|---|
| `expList_eq_avg_ofFn (T : ℕ) (F : List α → ℝ) : expList α T F = avg (fun ω : Fin T → α => F (List.ofFn ω))` | prob/equivalence.v | `expList_eq_avg_tuple (T : finType) k (F : seq T -> R) : expList k F = avg (fun w : k.-tuple T => F w)` | Product space `Fin T → α` → `k.-tuple T` (the `finType` of length-`k` sequences; `Fin k → T ≃ k.-tuple T` via `List.ofFn`/`tval`, both bijections onto length-`k` lists). `List.ofFn ω` → the coercion `tval w`. [L][S]. `avg` on `k.-tuple T` is `avg` on `Fin k → α` transported along that bijection (`avg_bij`). |

## 3. `3-majority/ThreeMajority/*.lean` (Lean namespace `ThreeMajority`)

### 3.1 `Prob.lean` → `theories/prob/avg.v`, `theories/prob/indep.v`

The first 19 declarations are verbatim copies of `RumorSpread/Prob.lean` (the two
Lake packages are independent); per decision D2 they share one Rocq port. The
statement differences are exactly those of §2.1.

| Lean name | Rocq file | Rocq name | Statement differences |
|---|---|---|---|
| `avg` | prob/avg.v | `avg` | as §2.1 |
| `avg_nonneg` | prob/avg.v | `avg_ge0` | as §2.1 |
| `avg_le_avg` | prob/avg.v | `avg_le` | as §2.1 |
| `avg_add` | prob/avg.v | `avgD` | as §2.1 |
| `avg_sub` | prob/avg.v | `avgB` | as §2.1 |
| `avg_const_mul` | prob/avg.v | `avgZ` | as §2.1 |
| `avg_sum` | prob/avg.v | `avg_sum` | as §2.1 ([G]) |
| `avg_indicator` | prob/avg.v | `avg_ind` | as §2.1 |
| `card_cast_pos` | prob/avg.v | `card_gt0R` | as §2.1 |
| `avg_const` | prob/avg.v | `avg_const` | as §2.1 |
| `expList` | prob/avg.v | `expList` | as §2.1 |
| `expList_zero` | prob/avg.v | `expList0` | as §2.1 |
| `expList_succ` | prob/avg.v | `expListS` | as §2.1 |
| `expList_nonneg` | prob/avg.v | `expList_ge0` | as §2.1 |
| `expList_le_expList` | prob/avg.v | `expList_le` | as §2.1 |
| `expList_add` | prob/avg.v | `expListD` | as §2.1 |
| `expList_const_mul` | prob/avg.v | `expListZ` | as §2.1 |
| `expList_const` | prob/avg.v | `expList_const` | as §2.1 |
| `expList_append` | prob/avg.v | `expList_cat` | as §2.1 |
| `avg_mul_prod (g : β → ℝ) (h : δ → ℝ) : avg (fun p : β × δ => g p.1 * h p.2) = avg g * avg h` | prob/indep.v | `avg_mul_prod (B D : finType) g h : avg (fun p : B * D => g p.1 * h p.2) = avg g * avg h` | none (no nonemptiness hypothesis on either side). |
| `avg_fst_mul [Nonempty δ] (g : β → ℝ) : avg (fun p : β × δ => g p.1) = avg g` | prob/indep.v | `avg_fst g : (0 < #\|D\|)%N -> avg (fun p : B * D => g p.1) = avg g` | [N]. |
| `avg_snd_mul [Nonempty β] (h : δ → ℝ) : avg (fun p : β × δ => h p.2) = avg h` | prob/indep.v | `avg_snd h : (0 < #\|B\|)%N -> avg (fun p : B * D => h p.2) = avg h` | [N]. |
| `avg_equiv (e : α ≃ β) (F : β → ℝ) : avg (fun a => F (e a)) = avg F` | prob/indep.v | `avg_bij (e : T -> U) (F : U -> R) : bijective e -> avg (fun a => F (e a)) = avg F` | [Eq]. |
| `avg_prod_pi : ∀ (n : ℕ) (f : Fin n → γ → ℝ), avg (fun x : Fin n → γ => ∏ i, f i (x i)) = ∏ i, avg (f i)` | prob/indep.v | `avg_prod_ffun (G : finType) n (f : 'I_n -> G -> R) : avg (fun x : {ffun 'I_n -> G} => \prod_(i < n) f i (x i)) = \prod_(i < n) avg (f i)` | `Fin n → γ` → `{ffun 'I_n -> G}` (the `finType` of finite functions; `card_ffun`). [F]. |
| `avg_eval [Nonempty γ] (n) (v : Fin n) (G : γ → ℝ) : avg (fun x : Fin n → γ => G (x v)) = avg G` | prob/indep.v | `avg_eval (G : finType) n (v : 'I_n) (F : G -> R) : (0 < #\|G\|)%N -> avg (fun x : {ffun 'I_n -> G} => F (x v)) = avg F` | [N][F]. |

### 3.2 `Model.lean` → `theories/majority/model.v`

| Lean name | Rocq file | Rocq name | Statement differences |
|---|---|---|---|
| `def Tgt3 (n : ℕ) := Fin n → Fin n × Fin n × Fin n` | majority/model.v | `Notation Tgt3 n := {ffun 'I_n -> 'I_n * ('I_n * 'I_n)}` | [F]; Lean's `×` is right-associative, so the nesting `Fin n × (Fin n × Fin n)` is preserved and `s.1`, `s.2.1`, `s.2.2` denote the same components. |
| `instance (n) : Fintype (Tgt3 n)` | — | — | Automatic (`{ffun _ -> _}` over `finType`s). |
| `instance (n) : DecidableEq (Tgt3 n)` | — | — | Automatic. |
| `tgt3_nonempty (hn : 1 ≤ n) : Nonempty (Tgt3 n)` | majority/model.v | `tgt3_gt0 : (1 <= n)%N -> (0 < #\|Tgt3 n\|)%N` | [N][Q]. Constant `1`. |
| `sampleCountOf I s : ℕ := (if s.1 ∈ I then 1 else 0) + (if s.2.1 ∈ I then 1 else 0) + (if s.2.2 ∈ I then 1 else 0)` | majority/model.v | `sampleCountOf I t : nat := (t.1 \in I) + (t.2.1 \in I) + (t.2.2 \in I)` | [F][I]. |
| `sampleCount I r v : ℕ := sampleCountOf I (r v)` | majority/model.v | `sampleCount I r v : nat := sampleCountOf I (r v)` | none. |
| `step I r := univ.filter (fun v => 2 ≤ sampleCount I r v)` | majority/model.v | `step I r : {set 'I_n} := [set v \| (2 <= sampleCount I r v)%N]` | [F]. Constant `2`. |
| `mem_step : v ∈ step I r ↔ 2 ≤ sampleCount I r v` | majority/model.v | `mem_step : (v \in step I r) = (2 <= sampleCount I r v)%N` | [B]. |
| `private ite_mem_mono (h : I ⊆ I') : (if x ∈ I then 1 else 0) ≤ (if x ∈ I' then 1 else 0)` | — | — | Proof device; inlined as the local fact `h` in the Rocq proof of `sampleCount_mono`. |
| `sampleCount_mono (h : I ⊆ I') r v : sampleCount I r v ≤ sampleCount I' r v` | majority/model.v | `sampleCount_mono I I' r v : I \subset I' -> (sampleCount I r v <= sampleCount I' r v)%N` | [F][Q]. |
| `step_mono (h : I ⊆ I') r : step I r ⊆ step I' r` | majority/model.v | `step_mono I I' r : I \subset I' -> step I r \subset step I' r` | [F][Q]. |
| `card_step_le I r : (step I r).card ≤ n` | majority/model.v | `card_step_le : (#\|step I r\| <= n)%N` | [F]. |
| `run I : List (Tgt3 n) → Finset (Fin n)` | majority/model.v | `Fixpoint run I s` | [L]; same recursion as §2.2. |
| `run_nil` | majority/model.v | `run_nil` | [L]. |
| `run_cons` | majority/model.v | `run_cons` | [L]. |
| `run_append I l₁ l₂ : run I (l₁ ++ l₂) = run (run I l₁) l₂` | majority/model.v | `run_cat` | [L]. |
| `run_mono (h : I ⊆ I') l : run I l ⊆ run I' l` | majority/model.v | `run_mono I I' s : I \subset I' -> run I s \subset run I' s` | [F][Q]. |

### 3.3 `OneRound.lean` → `theories/majority/oneround.v`

| Lean name | Rocq file | Rocq name | Statement differences |
|---|---|---|---|
| `ind I x : ℝ := if x ∈ I then 1 else 0` | majority/oneround.v | `ind I x : R := (x \in I)%:R` | [I]. |
| `ind_eq_zero_or_one I x : ind I x = 0 ∨ ind I x = 1` | majority/oneround.v | `ind01` | none. |
| `avg_ind I : avg (ind I) = (I.card : ℝ) / (Fintype.card (Fin n) : ℝ)` | majority/oneround.v | `avg_ind I : avg (ind I) = #\|I\|%:R / #\|'I_n\|%:R` | [F]. (Shadows `Dynamics.prob.avg.avg_ind` inside `majority/`; name only.) |
| `avg_ind_eq I : avg (ind I) = (I.card : ℝ) / n` | majority/oneround.v | `avg_indE I : avg (ind I) = #\|I\|%:R / n%:R` | [F]. |
| `majorityIndicator_eq I s : (if 2 ≤ sampleCountOf I s then (1:ℝ) else 0) = ind I s.1 * ind I s.2.1 + ind I s.2.1 * ind I s.2.2 + ind I s.1 * ind I s.2.2 - 2 * (ind I s.1 * ind I s.2.1 * ind I s.2.2)` | majority/oneround.v | `majorityIndicatorE I t : ((2 <= sampleCountOf I t)%N)%:R = ind I t.1 * ind I t.2.1 + ind I t.2.1 * ind I t.2.2 + ind I t.1 * ind I t.2.2 - 2 * (ind I t.1 * ind I t.2.1 * ind I t.2.2)` | [I]. Constant `2`. |
| `avg_ind_mul_fst_snd1 I [Nonempty (Fin n)] : avg (fun s => ind I s.1 * ind I s.2.1) = avg (ind I) * avg (ind I)` | majority/oneround.v | `avg_ind_mul_fst_snd1 I : (0 < n)%N -> ...` (same equation) | [N] (`Nonempty (Fin n)` ↔ `0 < n`). |
| `avg_ind_mul_snd1_snd2 I [Nonempty (Fin n)]` | majority/oneround.v | `avg_ind_mul_snd1_snd2 I : (0 < n)%N -> ...` | [N]. |
| `avg_ind_mul_fst_snd2 I [Nonempty (Fin n)]` | majority/oneround.v | `avg_ind_mul_fst_snd2 I : (0 < n)%N -> ...` | [N]. |
| `avg_ind_mul_triple I [Nonempty (Fin n)] : avg (fun s => ind I s.1 * ind I s.2.1 * ind I s.2.2) = avg (ind I) * avg (ind I) * avg (ind I)` | majority/oneround.v | `avg_ind_mul_triple I : (0 < n)%N -> ...` | [N]; the hypothesis is unused in both proofs and kept for fidelity. |
| `Y_maj I (_ : Fin n) s : ℝ := if 2 ≤ sampleCountOf I s then 1 else 0` | majority/oneround.v | `Y_maj I (v : 'I_n) t : R := ((2 <= sampleCountOf I t)%N)%:R` | [I]; the agent index is unused in both. |
| `Y_maj_zero_one I v s : Y_maj I v s = 0 ∨ Y_maj I v s = 1` | majority/oneround.v | `Y_maj01` | none. |
| `card_step_eq_sum I r : ((step I r).card : ℝ) = ∑ v : Fin n, Y_maj I v (r v)` | majority/oneround.v | `card_step_eq_sum I r : #\|step I r\|%:R = \sum_(v < n) Y_maj I v (r v) :> R` | [F]. |
| `avg_Y_maj_eq I [Nonempty (Fin n)] v : avg (Y_maj I v) = avg (ind I) * avg (ind I) * 3 - 2 * (avg (ind I) * avg (ind I) * avg (ind I))` | majority/oneround.v | `avg_Y_majE I v : (0 < n)%N -> ...` (same equation) | [N]. Constants `3, 2`. |
| `sum_avg_Y_maj (hn : 1 ≤ n) I : ∑ v, avg (Y_maj I v) = (n:ℝ) * (3 * (avg (ind I))^2 - 2 * (avg (ind I))^3)` | majority/oneround.v | `sum_avg_Y_maj I : (1 <= n)%N -> \sum_(v < n) avg (Y_maj I v) = n%:R * (3 * avg (ind I) ^+ 2 - 2 * avg (ind I) ^+ 3)` | [Q]. |
| `avg_card_step (hn : 1 ≤ n) I : avg (fun r => ((step I r).card : ℝ)) = (n:ℝ) * (3 * (avg (ind I))^2 - 2 * (avg (ind I))^3)` | majority/oneround.v | `avg_card_step I : (1 <= n)%N -> avg (fun r => #\|step I r\|%:R : R) = n%:R * (3 * avg (ind I) ^+ 2 - 2 * avg (ind I) ^+ 3)` | [F][Q]. |
| `Y_dis I v s : ℝ := 1 - Y_maj I v s` | majority/oneround.v | `Y_dis I v t : R := 1 - Y_maj I v t` | none. |
| `Y_dis_zero_one` | majority/oneround.v | `Y_dis01` | none. |
| `card_dissent_eq_sum I r : ((n:ℝ) - (step I r).card) = ∑ v, Y_dis I v (r v)` | majority/oneround.v | `card_dissent_eq_sum I r : n%:R - #\|step I r\|%:R = \sum_(v < n) Y_dis I v (r v) :> R` | [F]. |
| `sum_avg_Y_dis (hn : 1 ≤ n) I : ∑ v, avg (Y_dis I v) = (n:ℝ) - (n:ℝ) * (3 * (avg (ind I))^2 - 2 * (avg (ind I))^3)` | majority/oneround.v | `sum_avg_Y_dis I : (1 <= n)%N -> \sum_(v < n) avg (Y_dis I v) = n%:R - n%:R * (3 * avg (ind I) ^+ 2 - 2 * avg (ind I) ^+ 3)` | [Q]. |

### 3.4 `Chernoff.lean` → `theories/prob/chernoff.v`

Rocq: `Section Chernoff` with `Context {R} {n} {G : finType}`, `Variable Y : 'I_n -> G -> R`,
`Hypothesis Y01 : forall i x, Y i x = 0 \/ Y i x = 1`, and local notations
`X x := \sum_(i < n) Y i (x i)`, `mu := \sum_(i < n) avg (Y i)`; Lean passes
`(Y : Fin n → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1)` explicitly to each lemma ([S]).

| Lean name | Rocq file | Rocq name | Statement differences |
|---|---|---|---|
| `avg_exp_le Y hY (t : ℝ) : avg (fun x : Fin n → γ => exp (t * ∑ i, Y i (x i))) ≤ exp ((∑ i, avg (Y i)) * (exp t - 1))` | prob/chernoff.v | `avg_exp_le (t : R) : avg (fun x : {ffun 'I_n -> G} => expR (t * X x)) <= expR (mu * (expR t - 1))` | [S][F][Nat]. |
| `avg_tail_ge Y hY {t} (ht : 0 ≤ t) (k : ℝ) : avg (fun x => if k ≤ ∑ i, Y i (x i) then 1 else 0) ≤ exp ((∑ avg (Y i)) * (exp t - 1) - t * k)` | prob/chernoff.v | `avg_tail_ge (t k : R) : 0 <= t -> avg (fun x => ((k <= X x)%R)%:R : R) <= expR (mu * (expR t - 1) - t * k)` | [S][I][Q]. |
| `avg_tail_le Y hY {t} (ht : t ≤ 0) k : avg (fun x => if ∑ i, Y i (x i) ≤ k then 1 else 0) ≤ exp (... - t * k)` | prob/chernoff.v | `avg_tail_le (t k : R) : t <= 0 -> avg (fun x => ((X x <= k)%R)%:R : R) <= expR (mu * (expR t - 1) - t * k)` | [S][I][Q]. |
| `avg_tail_ge_log Y hY {k μ} (hμ : μ = ∑ avg (Y i)) (hμ0 : 0 < μ) (hk : μ ≤ k) : avg (if k ≤ ∑ ...) ≤ exp (k - μ - k * log (k / μ))` | prob/chernoff.v | `avg_tail_ge_ln (k m : R) : m = mu -> 0 < m -> m <= k -> avg (...) <= expR (k - m - k * ln (k / m))` | [S][I][Q]; same three hypotheses in the same order. |
| `avg_tail_le_log Y hY {k μ} (hμ : μ = ∑ avg (Y i)) (hk0 : 0 < k) (hkμ : k ≤ μ) : avg (if ∑ ... ≤ k) ≤ exp (k - μ - k * log (k / μ))` | prob/chernoff.v | `avg_tail_le_ln (k m : R) : m = mu -> 0 < k -> k <= m -> ...` | [S][I][Q]. |
| `avg_tail_ge_log_le Y hY {k μub} (hμ : ∑ avg (Y i) ≤ μub) (hμub0 : 0 < μub) (hk : μub ≤ k) : ... ≤ exp (k - μub - k * log (k / μub))` | prob/chernoff.v | `avg_tail_ge_ln_le (k mub : R) : mu <= mub -> 0 < mub -> mub <= k -> ...` | [S][I][Q]. |
| `avg_tail_le_log_ge Y hY {k μlb} (hμ : μlb ≤ ∑ avg (Y i)) (hk0 : 0 < k) (hkμ : k ≤ μlb) : ... ≤ exp (k - μlb - k * log (k / μlb))` | prob/chernoff.v | `avg_tail_le_ln_ge (k mlb : R) : mlb <= mu -> 0 < k -> k <= mlb -> ...` | [S][I][Q]. |

### 3.5 `Growth.lean` → `theories/majority/growth.v`

| Lean name | Rocq file | Rocq name | Statement differences |
|---|---|---|---|
| `growthBias (j : ℕ) : ℝ := (1 / 10) * (11 / 10) ^ j` | majority/growth.v | `growthBias (j : nat) : R := 1 / 10 * (11 / 10) ^+ j` | none. Constants `1/10, 11/10`. |
| `growthBias_zero : growthBias 0 = 1 / 10` | majority/growth.v | `growthBias0` | none. |
| `growthBias_nonneg j : 0 ≤ growthBias j` | majority/growth.v | `growthBias_ge0` | none. |
| `growthBias_mono j : growthBias j ≤ growthBias (j + 1)` | majority/growth.v | `growthBias_leS j : growthBias j <= growthBias j.+1` | none. |
| `growthBias_le_of_le {i j} (h : i ≤ j) : growthBias i ≤ growthBias j` | majority/growth.v | `growthBias_le i j : (i <= j)%N -> growthBias i <= growthBias j` | [Q]. |
| `growthBias_le_quarter {j} (hj : j ≤ 9) : growthBias j ≤ 1 / 4` | majority/growth.v | `growthBias_le_quarter j : (j <= 9)%N -> growthBias j <= 1 / 4` | [Q]. Constants `9, 1/4`. |
| `growthBias_ten : growthBias 10 > 1 / 4` | majority/growth.v | `growthBias10 : 1 / 4 < growthBias 10` | `>` written as the flipped `<`. Constants `10, 1/4`. |
| `growth_round (hn : 1 ≤ n) I {β} (hβ0 : 1/10 ≤ β) (hβ1 : β ≤ 1/4) (hI : (n:ℝ) * (1/2 + β) ≤ I.card) : avg (fun r => if ((step I r).card : ℝ) ≤ n * (1/2 + (11/10) * β) then 1 else 0) ≤ exp (-(1 / 10 ^ 7) * n)` | majority/growth.v | `growth_round I (b : R) : (1 <= n)%N -> 1 / 10 <= b -> b <= 1 / 4 -> n%:R * (1 / 2 + b) <= #\|I\|%:R -> avg (fun r => ((#\|step I r\|%:R <= n%:R * (1 / 2 + 11 / 10 * b))%R)%:R : R) <= expR (- (1 / 10 ^+ 7) * n%:R)` | [F][I][Q]. Constants `1/10, 1/4, 1/2, 11/10, 1/10^7`. |
| `growth_fail_le (hn : 1 ≤ n) (j : ℕ) : ∀ i, i + j ≤ 10 → ∀ I, (n:ℝ) * (1/2 + growthBias i) ≤ I.card → expList (Tgt3 n) j (fun l => if n * (1/2 + growthBias (i + j)) ≤ (run I l).card then 0 else 1) ≤ j * exp (-(1 / 10 ^ 7) * n)` | majority/growth.v | `growth_fail_le j : (1 <= n)%N -> forall i, (i + j <= 10)%N -> forall I, n%:R * (1 / 2 + growthBias i) <= #\|I\|%:R -> expList j (fun s => ((n%:R * (1 / 2 + growthBias (i + j)) <= #\|run I s\|%:R)%R == false)%:R : R) <= j%:R * expR (- (1 / 10 ^+ 7) * n%:R)` | [F][I] (`if P then 0 else 1` is the indicator of `~~ P`, written `(P == false)%:R`), [Q]; quantifier order `j, i, I` identical. Constants `10, 1/2, 1/10^7`. |
| `growth_phase1 (hn : 1 ≤ n) I₀ (hI₀ : (n:ℝ) * (3/5) ≤ I₀.card) : expList (Tgt3 n) 10 (fun l => if n * (3/4) ≤ (run I₀ l).card then 0 else 1) ≤ 10 * exp (-(1 / 10 ^ 7) * n)` | majority/growth.v | `growth_phase1 I0 : (1 <= n)%N -> n%:R * (3 / 5) <= #\|I0\|%:R :> R -> expList 10 (fun s => ((n%:R * (3 / 4) <= #\|run I0 s\|%:R :> R) == false)%:R : R) <= 10 * expR (- (1 / 10 ^+ 7) * n%:R)` | [F][I][Q]. Constants `3/5, 10, 3/4, 1/10^7`. |

### 3.6 `Saturation.lean` → `theories/majority/saturation.v`

| Lean name | Rocq file | Rocq name | Statement differences |
|---|---|---|---|
| `saturation_round_closed (hn : 1 ≤ n) I {M k} (hM0 : 0 < M) (hM1 : M ≤ n/4) (hkM : (5/8) * M ≤ k) (hUI : (n:ℝ) - I.card ≤ M) : avg (fun r => if k ≤ n - (step I r).card then 1 else 0) ≤ exp (k - (5/8) * M - k * log (k / ((5/8) * M)))` | majority/saturation.v | `saturation_round_closed I (M k : R) : (1 <= n)%N -> 0 < M -> M <= n%:R / 4 -> 5 / 8 * M <= k -> n%:R - #\|I\|%:R <= M -> avg (fun r => ((k <= n%:R - #\|step I r\|%:R :> R))%:R : R) <= expR (k - 5 / 8 * M - k * ln (k / (5 / 8 * M)))` | [F][I][Q]. Constants `4, 5/8`. |
| `saturation_round_generic (hn : 1 ≤ n) I {μub k} (hμub0 : 0 < μub) (hkμ : μub ≤ k) (hμ : ∑ v, avg (Y_dis I v) ≤ μub) : avg (...) ≤ exp (k - μub - k * log (k / μub))` | majority/saturation.v | `saturation_round_generic I (mub k : R) : (1 <= n)%N -> 0 < mub -> mub <= k -> \sum_(v < n) avg (Y_dis I v) <= mub -> avg (...) <= expR (k - mub - k * ln (k / mub))` | [F][I][Q]. |
| `saturation_mean_quad (hn1 : 1 ≤ n) I {M} (hM0 : 0 ≤ M) (hUI : (n:ℝ) - I.card ≤ M) : ∑ v, avg (Y_dis I v) ≤ 3 * M ^ 2 / n` | majority/saturation.v | `saturation_mean_quad I (M : R) : (1 <= n)%N -> 0 <= M -> n%:R - #\|I\|%:R <= M -> \sum_(v < n) avg (Y_dis I v) <= 3 * M ^+ 2 / n%:R` | [F][Q]. Constant `3`. |
| `saturation_round_numeric (hn) I {M k} (hM0 : 0 < M) (hM1 : M ≤ n/4) (hkM : (5/8) * M ≤ k) (hk0 : 0 < k) (hUI) : avg (...) ≤ exp (-(k - (5/8) * M) ^ 2 / (k + (5/8) * M))` | majority/saturation.v | `saturation_round_numeric I (M k : R) : (1 <= n)%N -> 0 < M -> M <= n%:R / 4 -> 5 / 8 * M <= k -> 0 < k -> n%:R - #\|I\|%:R <= M -> avg (...) <= expR (- (k - 5 / 8 * M) ^+ 2 / (k + 5 / 8 * M))` | [F][I][Q]; `-a^2/b` parses as `(-(a^2))/b` in both. Constants `4, 5/8`. |
| `saturation_round_contract (hn) I {M} (hM0 : 0 < M) (hM1 : M ≤ n/4) (hUI) : avg (fun r => if (7/10) * M ≤ n - (step I r).card then 1 else 0) ≤ exp (-(1/250) * M)` | majority/saturation.v | `saturation_round_contract I (M : R) : (1 <= n)%N -> 0 < M -> M <= n%:R / 4 -> n%:R - #\|I\|%:R <= M -> avg (fun r => ((7 / 10 * M <= n%:R - #\|step I r\|%:R :> R))%:R : R) <= expR (- (1 / 250) * M)` | [F][I][Q]. Constants `4, 7/10, 1/250`. |
| `satAfter (n) (M : ℝ) (i : ℕ) : ℝ := max (500 * log n) ((7/10) ^ i * M)` | majority/saturation.v | `satAfter (M : R) (i : nat) : R := Num.max (500 * ln n%:R) ((7 / 10) ^+ i * M)` | [S][Nat]. Constants `500, 7/10`. |
| `satAfter_ge_floor n M i : 500 * log n ≤ satAfter n M i` | majority/saturation.v | `satAfter_ge_floor M i : 500 * ln n%:R <= satAfter M i` | [S]. |
| `satAfter_zero n M (hM : 500 * log n ≤ M) : satAfter n M 0 = M` | majority/saturation.v | `satAfter0 M : 500 * ln n%:R <= M -> satAfter M 0 = M` | [S][Q]. |
| `satAfter_le_of_le (hM0 : 0 ≤ M) (hM1 : M ≤ n/4) (hfloor4 : 500 * log n ≤ n/4) i : satAfter n M i ≤ n/4` | majority/saturation.v | `satAfter_le M i : 0 <= M -> M <= n%:R / 4 -> 500 * ln n%:R <= n%:R / 4 :> R -> satAfter M i <= n%:R / 4` | [S][Q]. |
| `satAfter_contract_le (hn1 : 1 ≤ n) M i : (7/10) * satAfter n M i ≤ satAfter n M (i + 1)` | majority/saturation.v | `satAfter_contract_le M i : (1 <= n)%N -> 7 / 10 * satAfter M i <= satAfter M i.+1` | [S][Q]. |
| `saturation_fail_le (hn2 : 2 ≤ n) {M} (hM0 : 500 * log n ≤ M) (hM1 : M ≤ n/4) (hfloor4 : 500 * log n ≤ n/4) (j : ℕ) : ∀ i I, (n:ℝ) - I.card ≤ satAfter n M i → expList (Tgt3 n) j (fun l => if satAfter n M (i + j) < n - (run I l).card then 1 else 0) ≤ j * exp (-2 * log n)` | majority/saturation.v | `saturation_fail_le (M : R) j : (2 <= n)%N -> 500 * ln n%:R <= M -> M <= n%:R / 4 -> 500 * ln n%:R <= n%:R / 4 :> R -> forall i I, n%:R - #\|I\|%:R <= satAfter M i -> expList j (fun s => ((satAfter M (i + j) < n%:R - #\|run I s\|%:R :> R))%:R : R) <= j%:R * expR (- 2 * ln n%:R)` | [F][I][Q]; same four hypotheses, same order, `∀ i I` after `j`. Constants `2, 500, 4, 2`. |
| `T2a (n : ℕ) : ℕ := ⌈6 * Real.log n⌉₊` | majority/saturation.v | `T2a : nat := ceiln (6 * ln (n%:R : R))`, exported as `T2a n R` (`Arguments T2a : clear implicits`) | [C][S]; `R` is an explicit argument because `nat` does not determine it. Constant `6`. |
| `satAfter_quarter_le_floor (hn2 : 2 ≤ n) : satAfter n (n/4) (T2a n) ≤ 500 * log n` | majority/saturation.v | `satAfter_quarter_le_floor : (2 <= n)%N -> satAfter (n%:R / 4) T2a <= 500 * ln n%:R` | [Q]. |
| `saturation_stage2a (hn2 : 2 ≤ n) (hfloor4 : 500 * log n ≤ n/4) I₀ (hI₀ : (n:ℝ) - I₀.card ≤ n/4) : expList (Tgt3 n) (T2a n) (fun l => if 500 * log n < n - (run I₀ l).card then 1 else 0) ≤ (T2a n) * exp (-2 * log n)` | majority/saturation.v | `saturation_stage2a I0 : (2 <= n)%N -> 500 * ln n%:R <= n%:R / 4 :> R -> n%:R - #\|I0\|%:R <= n%:R / 4 :> R -> expList T2a (fun s => ((500 * ln n%:R < n%:R - #\|run I0 s\|%:R :> R))%:R : R) <= T2a%:R * expR (- 2 * ln n%:R)` | [F][I][Q]. Constants `500, 4, 2`. |
| `saturation_stage2b (hbig : 30 ≤ log n) I (hUI : (n:ℝ) - I.card ≤ 500 * log n) : avg (fun r => if 10 ≤ n - (step I r).card then 1 else 0) ≤ exp (-log n)` | majority/saturation.v | `saturation_stage2b I : 30 <= ln n%:R :> R -> n%:R - #\|I\|%:R <= 500 * ln n%:R :> R -> avg (fun r => ((10 <= n%:R - #\|step I r\|%:R :> R))%:R : R) <= expR (- ln n%:R)` | [F][I][Q]. Constants `30, 500, 10`. |
| `saturation_stage2c (hn1 : 1 ≤ n) I (hUI : (n:ℝ) - I.card ≤ 10) : avg (fun r => if 1 ≤ n - (step I r).card then 1 else 0) ≤ 300 / n` | majority/saturation.v | `saturation_stage2c I : (1 <= n)%N -> n%:R - #\|I\|%:R <= 10 :> R -> avg (fun r => ((1 <= n%:R - #\|step I r\|%:R :> R))%:R : R) <= 300 / n%:R` | [F][I][Q]. Constants `10, 1, 300`. |

### 3.7 `Bounds.lean` → `theories/prob/bounds.v`

| Lean name | Rocq file | Rocq name | Statement differences |
|---|---|---|---|
| `log_ge_quadratic (hx0 : 1/2 ≤ x) (hx1 : x ≤ 1) : (x - 1) - (x - 1) ^ 2 ≤ Real.log x` | prob/bounds.v | `ln_ge_quadratic x : 1 / 2 <= x -> x <= 1 -> (x - 1) - (x - 1) ^+ 2 <= ln x` | [Nat][Q]. |
| `exp_ge_pow (hx : 0 ≤ x) (k : ℕ) : x ^ k / k.factorial ≤ Real.exp x` | prob/bounds.v | ``expR_ge_pow x k : 0 <= x -> x ^+ k / k`!%:R <= expR x`` | [Nat][Q]. |
| `exp_ge_cube (hx : 0 ≤ x) : x ^ 3 / 6 ≤ Real.exp x` | prob/bounds.v | `expR_ge_cube x : 0 <= x -> x ^+ 3 / 6 <= expR x` | [Nat][Q]. |
| `log_le_tangent_div (hL : 0 < L) (hc : 0 < c) : Real.log L ≤ Real.log c - 1 + L / c` | prob/bounds.v | `ln_le_tangent_div L c : 0 < L -> 0 < c -> ln L <= ln c - 1 + L / c` | [Nat][Q]. |
| `exp_three_ge_twenty : (20 : ℝ) ≤ Real.exp 3` | prob/bounds.v | `expR3_ge20 : (20 : R) <= expR 3` | [Nat]. |
| `log_log_le_of_pos (hx : 0 < Real.log x) : Real.log (Real.log x) ≤ 2 + Real.log x / 20` | prob/bounds.v | `ln_ln_le x : 0 < ln x -> ln (ln x) <= 2 + ln x / 20` | [Nat][Q]. Constants `2, 20`. |
| `two_le_of_hbig (hbig : (30 : ℝ) ≤ Real.log n) : 2 ≤ n` | prob/bounds.v | `two_le_of_ln_ge30 n : 30 <= ln (n%:R : R) -> (2 <= n)%N` | [Nat][Q]. |

### 3.8 `Main.lean` → `theories/majority/main.v`

| Lean name | Rocq file | Rocq name | Statement differences |
|---|---|---|---|
| `ne_univ_iff_pos_dissent I : I ≠ univ ↔ (1 : ℝ) ≤ (n : ℝ) - (I.card : ℝ)` | majority/main.v | `neq_setT_dissent I : (I != [set: 'I_n]) = (1 <= n%:R - #\|I\|%:R :> R)` | [B] (iff of two decidable propositions as a `bool` equation), [F]. |
| `hfloor4_of_hbig (hbig : (30 : ℝ) ≤ Real.log n) : 500 * Real.log n ≤ (n : ℝ) / 4` | majority/main.v | `floor4_of_big : 30 <= ln (n%:R : R) -> 500 * ln n%:R <= n%:R / 4 :> R` | [Q]. Constants `30, 500, 4`. |
| `saturation_2b2c (hbig) I (hUI : (n:ℝ) - I.card ≤ 500 * log n) : expList (Tgt3 n) 2 (fun l => if 1 ≤ n - (run I l).card then 1 else 0) ≤ exp (-log n) + 300 / n` | majority/main.v | `saturation_2b2c I : 30 <= ln (n%:R : R) -> n%:R - #\|I\|%:R <= 500 * ln n%:R :> R -> expList 2 (fun s => ((1 <= n%:R - #\|run I s\|%:R :> R))%:R : R) <= expR (- ln n%:R) + 300 / n%:R` | [F][I][Q]. Constants `30, 500, 2, 1, 300`. |
| `saturation_2a2b2c (hbig) I₀ (hI₀ : (n:ℝ) - I₀.card ≤ n/4) : expList (Tgt3 n) (T2a n + 2) (fun l => if 1 ≤ n - (run I₀ l).card then 1 else 0) ≤ (T2a n) * exp (-2 * log n) + (exp (-log n) + 300 / n)` | majority/main.v | `saturation_2a2b2c I0 : 30 <= ln (n%:R : R) -> n%:R - #\|I0\|%:R <= n%:R / 4 :> R -> expList (T2a n R + 2) (fun s => ((1 <= n%:R - #\|run I0 s\|%:R :> R))%:R : R) <= (T2a n R)%:R * expR (- 2 * ln n%:R) + (expR (- ln n%:R) + 300 / n%:R)` | [F][I][Q]. Constants `30, 4, 2, 1, 2, 300`. |
| `theorem majority3_consensus_fail_le (hbig : (30:ℝ) ≤ Real.log n) I₀ (hI₀ : (n:ℝ) * (3/5) ≤ I₀.card) : expList (Tgt3 n) (10 + (T2a n + 2)) (fun l => if (1:ℝ) ≤ n - (run I₀ l).card then 1 else 0) ≤ 10 * exp (-(1 / 10 ^ 7) * n) + ((T2a n) * exp (-2 * log n) + (exp (-log n) + 300 / n))` | majority/main.v | `Theorem majority3_consensus_fail_le I0 : 30 <= ln (n%:R : R) -> n%:R * (3 / 5) <= #\|I0\|%:R :> R -> expList (10 + (T2a n R + 2)) (fun s => ((1 <= n%:R - #\|run I0 s\|%:R :> R))%:R : R) <= 10 * expR (- (1 / 10 ^+ 7) * n%:R) + ((T2a n R)%:R * expR (- 2 * ln n%:R) + (expR (- ln n%:R) + 300 / n%:R))` | [F][I][Q]. Constants `30, 3/5, 10, 2, 1, 1/10^7, 2, 300`. |
| `theorem majority3_consensus_fail_le_clean (hbig) I₀ (hI₀ : (n:ℝ) * (3/5) ≤ I₀.card) : expList (Tgt3 n) (10 + (T2a n + 2)) (fun l => if (1:ℝ) ≤ n - (run I₀ l).card then 1 else 0) ≤ 500 / n` | majority/main.v | `Theorem majority3_consensus_fail_le_clean I0 : 30 <= ln (n%:R : R) -> n%:R * (3 / 5) <= #\|I0\|%:R :> R -> expList (10 + (T2a n R + 2)) (fun s => ((1 <= n%:R - #\|run I0 s\|%:R :> R))%:R : R) <= 500 / n%:R` | [F][I][Q]. Constants `30, 3/5, 10, 2, 500`. |
| `theorem majority3_consensus_whp (hbig : (30:ℝ) ≤ Real.log n) I₀ (hI₀ : (n:ℝ) * (3/5) ≤ I₀.card) : 1 - 500 / (n:ℝ) ≤ expList (Tgt3 n) (10 + (T2a n + 2)) (fun l => if run I₀ l = univ then (1:ℝ) else 0)` | majority/main.v | `Theorem majority3_consensus_whp I0 : 30 <= ln (n%:R : R) -> n%:R * (3 / 5) <= #\|I0\|%:R :> R -> 1 - 500 / n%:R <= expList (10 + (T2a n R + 2)) (fun s => (run I0 s == [set: 'I_n])%:R : R)` | [C] (inside `T2a`), [F][I][Q] only. Constants `30, 3/5, 500, 10, 2` (and `6` inside `T2a`); hypotheses `30 ≤ log n`, `n·(3/5) ≤ |I₀|`. |

## 4. Rocq declarations with no Lean counterpart

Each is a helper whose Lean role is played by a Mathlib lemma, by an inline
tactic, or by a proof device that the Rocq proof does not need. None appears in a
statement of §2–§3 except `ceiln` (see tag [C]) and `T2a`'s use of it.

| Rocq file | Name | Justification |
|---|---|---|
| prelude.v | ``ceiln (x : R) : nat := `\|Num.ceil x\|`` | Mathlib's `Nat.ceil` has no MathComp counterpart (`Num.ceil` is `int`-valued); equal to `Nat.ceil` for `x >= 0`, which covers every use ([C]). |
| prelude.v | `prelude_classical`, `prelude_reals`, `prelude_expR`, `prelude_ln`, `prelude_bigop`, `prelude_lra`, `prelude_lia`, `prelude_smoke` | Toolchain smoke checks (one per dependency), audited by `verify.sh`; not mathematics of the port. |
| prob/bounds.v | `expR_ge_series x n : 0 <= x -> series (exp_coeff x) n <= expR x` | Mathlib's `Real.sum_le_exp_of_nonneg`, used by Lean's `log_ge_quadratic`, `exp_ge_pow`; MathComp only ships the one-term truncation `expR_ge1Dxn`. |
| prob/bounds.v | `expR_ge_taylor2 x : 0 <= x -> 1 + x + x ^+ 2 / 2 <= expR x` | The degree-3 instance Lean obtains inline by `Real.sum_le_exp_of_nonneg hs0 3` + `norm_num`. |
| prob/indep.v | — | (all six declarations have Lean counterparts) |
| prob/equivalence.v | `avg_pair (G : B -> D -> R) : avg (fun p : B * D => G p.1 p.2) = avg (fun b => avg (fun d => G b d))` | Fubini for `avg` over a binary product; Lean does it inline with `Fintype.sum_prod_type` + `Finset.sum_div` in `expList_eq_avg_ofFn`. |
| prob/equivalence.v | `cons_tuple_bij T k : bijective (fun p : T * k.-tuple T => cons_tuple p.1 p.2)` | Mathlib's `Fin.consEquiv` (an `Equiv`), used by Lean's `expList_eq_avg_ofFn` and `avg_prod_pi`. |
| rumor/oneround.v | `foldr_muln_map g s : foldr muln 1 [seq g v \| v <- s] = (\prod_(v <- s) g v)%N` | Converts the `foldr muln` shape in which `card_dep_ffun`/`card_family` return dependent-function cardinalities into a bigop; Lean's `Fintype.card_pi` already returns `∏`. |
| rumor/main.v | `ln2_le : ln (2 : R) <= 7 / 10` | Mathlib's `Real.log_two_lt_d9` (`log 2 < 0.6931471808`), used by Lean's `numeric_B`; `7/10` suffices for the constants `9, 117, 23`. |
| rumor/main.v | `ceiln_ge x : 0 <= x -> x <= (ceiln x)%:R` | Mathlib's `Nat.le_ceil`. |
| rumor/main.v | `ceiln_lt x : 0 <= x -> (ceiln x)%:R < x + 1` | Mathlib's `Nat.ceil_lt_add_one`. |
| majority/saturation.v | `expR_pade t : 0 <= t -> 2 * (expR t - 1) <= t * (expR t + 1)` | Ingredient for `ln_ge_pade`; proved by the mean value theorem (`MVT_segment`, `is_derive`) from `mathcomp.analysis.derive`. |
| majority/saturation.v | `ln_ge_pade x : 1 <= x -> 2 * (x - 1) <= ln x * (x + 1)` | Mathlib's `Real.le_log_one_add_of_nonneg` (`2x/(x+2) <= log (1+x)`), multiplied out; used by Lean's `saturation_round_numeric`. MathComp-Analysis has no counterpart. |

## 5. Proof-level deviations

These change *how* a lemma is proved, never *what* is stated; the statements above
are unaffected. They are recorded in `CHANGELOG.md` and in the file headers.

1. **Numerics without `11!`** (`majority/saturation.v`, `majority/main.v`). Lean
   evaluates `Nat.factorial 11 = 39916800` by `norm_num` in `saturation_stage2b`,
   `hfloor4_of_hbig` and `majority3_consensus_fail_le_clean`. In Rocq large
   numerals are unary `nat` terms under `%:R` and overflow `lra`, so
   `saturation_stage2b` keeps `expR_ge_pow 11` symbolic (`!factS fact0 !natrM`),
   `floor4_of_big` uses the degree-5 term instead of degree 11, and
   `majority3_consensus_fail_le_clean` uses degree 14 (giving `n >= 5·10^9` rather
   than Lean's `4·10^8`) and degree 5 for the term `10 exp(-n/10^7) <= 1/n`. Same
   conclusions, same constants.
2. **Padé bound via the mean value theorem** (`majority/saturation.v`). Lean's
   `saturation_round_numeric` cites Mathlib's `Real.le_log_one_add_of_nonneg`. The
   port proves the equivalent `ln_ge_pade` from `expR_pade`, itself proved with
   `MVT_segment` — the one place the Rocq development uses calculus (Lean's
   `Bounds.lean` header advertises "none requiring calculus", which holds for the
   Lean side only because Mathlib supplies the bound). Only `majority/saturation.v`
   imports `mathcomp.analysis.derive`.
3. **`ln 2 <= 7/10`** (`rumor/main.v`, `majority/saturation.v`). Lean's `numeric_B`
   uses `Real.log_two_lt_d9` (ten digits); the port uses `ln2_le` from
   `expR_ge_series 4` at `7/10`, which is enough because `9·(7/10) + 1 <= 117/16`.
   Lean's `satAfter_quarter_le_floor` uses `Real.log_two_gt_d9` (`0.6931 <= log n`);
   the port uses `1/2 <= ln 2` from `one_sub_inv_le_ln`.
4. **Stage 2b without `ln 75000`** (`majority/saturation.v`). Lean rewrites
   `log (10/μ) = L - log 75000 - 2 log L` and bounds `log 75000 <= 12` via `2^17`.
   The port avoids the literal `75000` (unary overflow) by `75000 L^2 <= L^6`
   (from `L^4 >= 30^4`), giving `ln (10/mub) >= L - 6 ln L`, then `ln_ln_le`.
5. **`bigA_distr_bigA` instead of hand induction** (`prob/indep.v`). Lean's
   `avg_prod_pi` is a recursive lemma over `n` using `Fin.consEquiv` and
   `avg_mul_prod`; the port's `avg_prod_ffun` is `bigA_distr_bigA` + `card_ffun`,
   `natrX`, `prodr_const`, `exprVn`.
6. **Counting by `family`** (`rumor/oneround.v`). Lean's `card_filter_not_contacted`
   goes through the explicit `Equiv` `notContactedEquiv` and `Fintype.card_pi`; the
   port rewrites the set as `family F` and uses `card_family` + `foldr_muln_map`.
   Likewise `card_tgt` uses `card_dep_ffun` in place of `Fintype.card_pi`.
7. **`e >= 163/60`** (`prob/bounds.v`). Lean's `exp_three_ge_twenty` cubes
   `Real.exp_one_gt_d9`; the port cubes `163/60 <= expR 1` from `expR_ge_series 6`.
8. **Empty sample spaces.** Lean's `avg_exp_le` and `expList_eq_avg_ofFn` case-split
   on `isEmpty_or_nonempty`; the port uses `posnP #|G|` (`avg_exp_le`) or needs no
   split at all (`expList_eq_avg_tuple`, because `avg_pair`/`avg_bij` hold
   unconditionally).

## 6. Verdict

Both headline theorems are statement-for-statement faithful ports.

- `RumorPush.push_informs_all_whp` ↔ `Dynamics.rumor.main.push_informs_all_whp`
  (and the complement form `push_informs_all_whp'`): hypothesis `2 ≤ n` on both
  sides; horizon `(⌈117 log n⌉₊ + 23) + ⌈6 log n⌉₊` on both sides, with `⌈·⌉₊`
  rendered as `ceiln`, which agrees with `Nat.ceil` on all arguments that occur
  (tag [C]); bound `2/n` on both sides; the event "some node uninformed" is the
  indicator of `run {v₀} l ≠ univ` on both sides. The remaining differences are
  `Finset (Fin n)` vs `{set 'I_n}`, `List` vs `seq`, `ℝ` vs `R : realType`, and
  the `if … then 1 else 0` vs `(…)%:R` indicator convention.
- `ThreeMajority.majority3_consensus_whp` ↔
  `Dynamics.majority.main.majority3_consensus_whp`: hypotheses `30 ≤ log n` and
  `n·(3/5) ≤ |I₀|` on both sides; horizon `10 + (T2a n + 2)` with
  `T2a n = ⌈6 log n⌉₊` on both sides; bound `1 - 500/n` on both sides; the event is
  the indicator of `run I₀ l = univ` on both sides. Same representation changes as
  above, plus `Fin n → Fin n × Fin n × Fin n` vs `{ffun 'I_n -> 'I_n * ('I_n * 'I_n)}`.

Across all 169 mapped declarations, no hypothesis was added, dropped, strengthened
or weakened; no constant or exponent was altered; quantifier order is preserved.
The only Rocq statements that are not literally equivalent to their Lean source are
strictly *more general* (`avg_sum`, tag [G]). Both `verify.sh` headline theorems
depend only on the three `boolp` axioms.
