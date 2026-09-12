(** * Dynamics.prob.bounds — elementary real inequalities

    Port of [RumorSpread/Bounds.lean] (Bernoulli-type bounds; the rumor
    proof never needs the exponential) and [ThreeMajority/Bounds.lean]
    (quadratically tight bounds on [ln] near [1], [x^k / k! <= exp x], and
    tangent-line bounds on [ln], which keep the threshold on [ln n] in the
    3-majority proof modest). None of these needs calculus. *)

From Dynamics Require Import prelude.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.


Section Bounds.
Context {R : realType}.
Implicit Types x : R.

(** ** From [RumorSpread/Bounds.lean] *)

(** Lean: [one_sub_mul_le_pow] — Bernoulli's inequality,
    [1 - m x <= (1 - x)^m] for [x <= 2]. *)
Lemma one_sub_mul_le_pow x (m : nat) : x <= 2 -> 1 - m%:R * x <= (1 - x) ^+ m.
Proof. Admitted.

(** Lean: [mul_sub_sq_le_one_sub_pow] — second-order (Bonferroni) lower bound
    [m x - m^2 x^2 / 2 <= 1 - (1 - x)^m] for [0 <= x <= 1]. *)
Lemma mul_sub_sq_le_one_sub_pow x (m : nat) :
  0 <= x -> x <= 1 -> m%:R * x - m%:R ^+ 2 * x ^+ 2 / 2 <= 1 - (1 - x) ^+ m.
Proof. Admitted.

(** Lean: [half_mul_le_one_sub_pow] — if [m x <= 1] then
    [m x / 2 <= 1 - (1 - x)^m]. *)
Lemma half_mul_le_one_sub_pow x (m : nat) :
  0 <= x -> x <= 1 -> m%:R * x <= 1 -> m%:R * x / 2 <= 1 - (1 - x) ^+ m.
Proof. Admitted.

(** Lean: [pow_one_sub_le_one_div] — [(1 - x)^m <= 1 / (1 + m x)], an
    [e]-free upper bound. *)
Lemma pow_one_sub_le_one_div x (m : nat) :
  0 <= x -> x <= 1 -> (1 - x) ^+ m <= 1 / (1 + m%:R * x).
Proof. Admitted.

(** Lean: [one_sub_inv_le_log] — [1 - 1/x <= ln x] for [0 < x]. *)
Lemma one_sub_inv_le_ln x : 0 < x -> 1 - 1 / x <= ln x.
Proof. Admitted.

(** ** From [ThreeMajority/Bounds.lean] *)

(** Lean: [log_ge_quadratic] — quadratically tight lower bound on [ln] on
    [[1/2, 1]]: [ln x >= (x - 1) - (x - 1)^2]. *)
Lemma ln_ge_quadratic x : 1 / 2 <= x -> x <= 1 -> (x - 1) - (x - 1) ^+ 2 <= ln x.
Proof. Admitted.

(** Lean: [exp_ge_pow] — [x^k / k! <= exp x] for [x >= 0]. *)
Lemma expR_ge_pow x (k : nat) : 0 <= x -> x ^+ k / k`!%:R <= expR x.
Proof. Admitted.

(** Lean: [exp_ge_cube] — [x^3 / 6 <= exp x] for [x >= 0]. *)
Lemma expR_ge_cube x : 0 <= x -> x ^+ 3 / 6 <= expR x.
Proof. Admitted.

(** Lean: [log_le_tangent_div] — tangent-line bound on [ln] at a reference
    point [c]: [ln L <= ln c - 1 + L / c]. *)
Lemma ln_le_tangent_div (L c : R) : 0 < L -> 0 < c -> ln L <= ln c - 1 + L / c.
Proof. Admitted.

(** Lean: [exp_three_ge_twenty] — [20 <= exp 3]. *)
Lemma expR3_ge20 : (20 : R) <= expR 3.
Proof. Admitted.

(** Lean: [log_log_le_of_pos] — [ln (ln x) <= 2 + ln x / 20] when [0 < ln x]. *)
Lemma ln_ln_le x : 0 < ln x -> ln (ln x) <= 2 + ln x / 20.
Proof. Admitted.

(** Lean: [two_le_of_hbig] — [30 <= ln n] already forces [2 <= n]. *)
Lemma two_le_of_ln_ge30 (n : nat) : 30 <= ln (n%:R : R) -> (2 <= n)%N.
Proof. Admitted.

End Bounds.
