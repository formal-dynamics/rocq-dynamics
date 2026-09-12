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
Proof.
move=> x2; have [x1|x1] := leP x 1.
  elim: m => [|m ih]; first by rewrite expr0 mul0r subr0.
  rewrite exprS -natr1 mulrDl mul1r; have := ler0n R m; nra.
case: m => [|[|m]]; first by rewrite expr0 mul0r subr0.
  by rewrite expr1 mul1r.
have : `|(1 - x) ^+ m.+2| <= 1.
  by rewrite normrX exprn_ile1 // ler_norml; apply/andP; split; lra.
rewrite ler_norml => /andP[h _].
have : (2 : R) <= m.+2%:R by rewrite ler_nat.
nra.
Qed.

(** Lean: [mul_sub_sq_le_one_sub_pow] — second-order (Bonferroni) lower bound
    [m x - m^2 x^2 / 2 <= 1 - (1 - x)^m] for [0 <= x <= 1]. *)
Lemma mul_sub_sq_le_one_sub_pow x (m : nat) :
  0 <= x -> x <= 1 -> m%:R * x - m%:R ^+ 2 * x ^+ 2 / 2 <= 1 - (1 - x) ^+ m.
Proof.
move=> x0 x1; elim: m => [|m ih]; first by rewrite expr0; lra.
have hb : 1 - m%:R * x <= (1 - x) ^+ m by apply: one_sub_mul_le_pow; lra.
have hbx := ler_wpM2r x0 hb.
rewrite [(1 - x) ^+ _]exprS -natr1.
by have := sqr_ge0 x; have := ler0n R m; lra.
Qed.

(** Lean: [half_mul_le_one_sub_pow] — if [m x <= 1] then
    [m x / 2 <= 1 - (1 - x)^m]. *)
Lemma half_mul_le_one_sub_pow x (m : nat) :
  0 <= x -> x <= 1 -> m%:R * x <= 1 -> m%:R * x / 2 <= 1 - (1 - x) ^+ m.
Proof.
move=> x0 x1 mx1; have := mul_sub_sq_le_one_sub_pow m x0 x1.
by have := mulr_ge0 (ler0n R m) x0; nra.
Qed.

(** Lean: [pow_one_sub_le_one_div] — [(1 - x)^m <= 1 / (1 + m x)], an
    [e]-free upper bound. *)
Lemma pow_one_sub_le_one_div x (m : nat) :
  0 <= x -> x <= 1 -> (1 - x) ^+ m <= 1 / (1 + m%:R * x).
Proof.
move=> x0 x1; have m0 := ler0n R m.
have hpos : 0 < 1 + m%:R * x by have := mulr_ge0 m0 x0; lra.
rewrite ler_pdivlMr //.
have hB : - x <= 2 by lra.
have h2 : 1 + m%:R * x <= (1 + x) ^+ m.
  by have := one_sub_mul_le_pow m hB; rewrite mulrN !opprK.
have hx1 : 0 <= 1 - x by lra.
apply: le_trans (ler_wpM2l (exprn_ge0 m hx1) h2) _.
by rewrite -exprMn; apply: exprn_ile1; nra.
Qed.

(** Lean: [one_sub_inv_le_log] — [1 - 1/x <= ln x] for [0 < x]. *)
Lemma one_sub_inv_le_ln x : 0 < x -> 1 - 1 / x <= ln x.
Proof.
move=> x0; have xV0 : 0 < x^-1 by rewrite invr_gt0.
have h1 : -1 < x^-1 - 1 by lra.
have := le_ln1Dx h1; rewrite addrCA subrr addr0 lnV ?posrE // div1r.
by move=> h; lra.
Qed.

(** ** From [ThreeMajority/Bounds.lean] *)

(** Partial sums of the exponential series bound [expR] from below for
    nonnegative arguments (Mathlib's [Real.sum_le_exp_of_nonneg]; MathComp
    only ships the single-term truncation [expR_ge1Dxn]). *)
Lemma expR_ge_series x n : 0 <= x -> series (exp_coeff x) n <= expR x.
Proof.
move=> x0; apply: nondecreasing_cvgn_le; last exact: is_cvg_series_exp_coeff.
exact: nondecreasing_series (fun k _ _ => exp_coeff_ge0 k x0).
Qed.

(** Degree-2 Taylor lower bound, [1 + x + x^2/2 <= expR x] for [0 <= x]. *)
Lemma expR_ge_taylor2 x : 0 <= x -> 1 + x + x ^+ 2 / 2 <= expR x.
Proof.
move=> x0; have := expR_ge_series 3 x0.
rewrite /series/= !big_nat_recr//= big_geq// /exp_coeff/= expr0 expr1.
rewrite (_ : 0`!%:R = 1 :> R) // (_ : 2`!%:R = 2 :> R) //.
by move=> h; lra.
Qed.

(** Lean: [log_ge_quadratic] — quadratically tight lower bound on [ln] on
    [[1/2, 1]]: [ln x >= (x - 1) - (x - 1)^2]. *)
Lemma ln_ge_quadratic x : 1 / 2 <= x -> x <= 1 -> (x - 1) - (x - 1) ^+ 2 <= ln x.
Proof.
move=> x12 x1; have x0 : 0 < x by lra.
set s := (1 - x) + (1 - x) ^+ 2.
have s0 : 0 <= s by rewrite /s; have := sqr_ge0 (1 - x); lra.
have h1 : 1 <= x * (1 + s + s ^+ 2 / 2).
  have h : 0 <= (1 - x) ^+ 2 * (1 - (1 - x) - (1 - x) ^+ 2 - (1 - x) ^+ 3).
    by apply: mulr_ge0 (sqr_ge0 _) _; have := sqr_ge0 (1 - x); nra.
  rewrite /s; lra.
have h2 : 1 <= x * expR s.
  exact: le_trans h1 (ler_wpM2l (ltW x0) (expR_ge_taylor2 s0)).
have h4 : expR (- s) <= x by rewrite expRN -div1r ler_pdivrMr ?expR_gt0.
have h5 : - s <= ln x by rewrite -(expRK (- s)) ler_ln ?posrE ?expR_gt0.
by rewrite /s in h5; lra.
Qed.

(** Lean: [exp_ge_pow] — [x^k / k! <= exp x] for [x >= 0]. *)
Lemma expR_ge_pow x (k : nat) : 0 <= x -> x ^+ k / k`!%:R <= expR x.
Proof.
case: k => [|k] x0.
  by rewrite expr0 fact0 divr1 -[leLHS]expR0 ler_expR.
by apply: (le_trans _ (expR_ge1Dxn k x0)); rewrite lerDr ler01.
Qed.

(** Lean: [exp_ge_cube] — [x^3 / 6 <= exp x] for [x >= 0]. *)
Lemma expR_ge_cube x : 0 <= x -> x ^+ 3 / 6 <= expR x.
Proof. exact: expR_ge_pow 3. Qed.

(** Lean: [log_le_tangent_div] — tangent-line bound on [ln] at a reference
    point [c]: [ln L <= ln c - 1 + L / c]. *)
Lemma ln_le_tangent_div (L c : R) : 0 < L -> 0 < c -> ln L <= ln c - 1 + L / c.
Proof.
move=> L0 c0; have h1 : -1 < L / c - 1 by have := divr_gt0 L0 c0; lra.
have := le_ln1Dx h1; rewrite addrCA subrr addr0 ln_div ?posrE //.
by move=> h; lra.
Qed.

(** Lean: [exp_three_ge_twenty] — [20 <= exp 3]. *)
Lemma expR3_ge20 : (20 : R) <= expR 3.
Proof.
have e1 : 163 / 60 <= expR (1 : R).
  have := expR_ge_series 6 (@ler01 R).
  rewrite /series/= !big_nat_recr//= big_geq// /exp_coeff/= !expr1n.
  rewrite (_ : 0`!%:R = 1 :> R) // (_ : 2`!%:R = 2 :> R) //.
  rewrite (_ : 3`!%:R = 6 :> R) // (_ : 4`!%:R = 24 :> R) //.
  rewrite (_ : 5`!%:R = 120 :> R) //.
  by move=> h; lra.
have e3 : expR 3 = expR 1 ^+ 3 :> R by rewrite -expRM_natl mulr1.
have h : (20 : R) <= (163 / 60) ^+ 3 by lra.
rewrite e3; apply: le_trans h _.
by rewrite ler_pXn2r ?nnegrE ?expR_ge0 //; lra.
Qed.

(** Lean: [log_log_le_of_pos] — [ln (ln x) <= 2 + ln x / 20] when [0 < ln x]. *)
Lemma ln_ln_le x : 0 < ln x -> ln (ln x) <= 2 + ln x / 20.
Proof.
move=> hx; have := ln_le_tangent_div hx (expR_gt0 3); rewrite expRK.
have h2 : ln x / expR 3 <= ln x / 20.
  by rewrite ler_pM2l // lef_pV2 ?posrE ?expR_gt0 ?expR3_ge20 //; lra.
by move=> h1; lra.
Qed.

(** Lean: [two_le_of_hbig] — [30 <= ln n] already forces [2 <= n]. *)
Lemma two_le_of_ln_ge30 (n : nat) : 30 <= ln (n%:R : R) -> (2 <= n)%N.
Proof.
case: n => [|[|n]] //.
  by rewrite mulr0n ln0 ?lexx // lern0.
by rewrite mulr1n ln1 lern0.
Qed.

End Bounds.
