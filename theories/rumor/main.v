(** * Dynamics.rumor.main — the push protocol informs [K_n] in [O(log n)] rounds

    Port of [RumorSpread/Main.lean]. Glues the growth phase to the
    saturation phase through the [expList] conditioning idiom
    ([expList_cat]), proves the three numeric lemmas fixing the constants,
    and states the main theorem with the same constants as Lean: for
    [n >= 2], after [(⌈117 ln n⌉ + 23) + ⌈6 ln n⌉] rounds the probability
    that some node is still uninformed is at most [2/n]. *)

From Dynamics Require Import prelude.
From Dynamics.prob Require Import avg bounds.
From Dynamics.rumor Require Import model oneround growth saturation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Main.
Context {R : realType}.

(** Lean's [⌈x⌉₊] ([Nat.ceil]) for [x >= 0]: the natural number
    [|Num.ceil x|]. (For negative [x] the two differ, but every use below has
    [x = c * ln n >= 0].) *)
Definition ceiln (x : R) : nat := `|Num.ceil x|.

Variable n : nat.

(** Lean: [prNotAllInformed n v₀ T] — probability that not all nodes are
    informed after [k] rounds, starting from the single node [v0]. *)
Definition prNotAllInformed (v0 : 'I_n) (k : nat) : R :=
  expList k (fun s : seq (Tgt n) => (run [set v0] s != [set: 'I_n])%:R).

(** Lean: [prNotAllInformed_le] — gluing the two phases. *)
Lemma prNotAllInformed_le (v0 : 'I_n) (L k1 k2 : nat) :
  (2 <= n)%N -> n%:R <= (9 / 8 : R) ^+ L ->
  prNotAllInformed v0 (k1 + k2)
    <= 2 ^+ L * (15 / 16) ^+ k1 + (2 / 3) ^+ k2 * n%:R.
Proof. Admitted.

(** Lean: [numeric_A]. *)
Lemma numeric_A :
  (2 <= n)%N -> n%:R <= (9 / 8 : R) ^+ (ceiln (9 * ln n%:R) + 1).
Proof. Admitted.

(** Lean: [numeric_B]. *)
Lemma numeric_B :
  (2 <= n)%N ->
  2 ^+ (ceiln (9 * ln n%:R) + 1) * (15 / 16 : R) ^+ (ceiln (117 * ln n%:R) + 23)
    <= 1 / n%:R.
Proof. Admitted.

(** Lean: [numeric_C]. *)
Lemma numeric_C :
  (2 <= n)%N -> (2 / 3 : R) ^+ ceiln (6 * ln n%:R) * n%:R <= 1 / n%:R.
Proof. Admitted.

(** Lean: [push_informs_all_whp] — the main theorem. *)
Theorem push_informs_all_whp (v0 : 'I_n) :
  (2 <= n)%N ->
  prNotAllInformed v0 ((ceiln (117 * ln n%:R) + 23) + ceiln (6 * ln n%:R))
    <= 2 / n%:R.
Proof. Admitted.

(** Lean: [push_informs_all_whp'] — the same, as a lower bound on the
    probability that everyone is informed. *)
Theorem push_informs_all_whp' (v0 : 'I_n) :
  (2 <= n)%N ->
  1 - 2 / n%:R
    <= expList ((ceiln (117 * ln n%:R) + 23) + ceiln (6 * ln n%:R))
         (fun s : seq (Tgt n) => (run [set v0] s == [set: 'I_n])%:R : R).
Proof. Admitted.

End Main.
