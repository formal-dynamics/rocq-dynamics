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

Variable n : nat.

(** Probability that not all nodes are informed after [k] rounds, starting from
    the single node [v0]. (Lean: [prNotAllInformed n v₀ T].) *)
Definition prNotAllInformed (v0 : 'I_n) (k : nat) : R :=
  expList k (fun s : seq (Tgt n) => (run [set v0] s != [set: 'I_n])%:R).

(** Gluing the two phases. (Lean: [prNotAllInformed_le].) *)
Lemma prNotAllInformed_le (v0 : 'I_n) (L k1 k2 : nat) :
  (2 <= n)%N -> n%:R <= (9 / 8 : R) ^+ L ->
  prNotAllInformed v0 (k1 + k2)
    <= 2 ^+ L * (15 / 16) ^+ k1 + (2 / 3) ^+ k2 * n%:R.
Proof.
move=> hn hL.
have T0 := tgt_gt0 hn.
have n0 : 0 <= n%:R :> R by rewrite ler0n.
have c0 : 0 <= (2 / 3 : R) ^+ k2 by apply: exprn_ge0; lra.
have B0 : 0 <= (2 / 3 : R) ^+ k2 * n%:R by apply: mulr_ge0.
rewrite /prNotAllInformed expList_cat.
have inner s1 :
    expList k2 (fun s2 => (run [set v0] (s1 ++ s2) != [set: 'I_n])%:R : R)
      <= ((2 * #|run [set v0] s1| <= n)%N)%:R + (2 / 3) ^+ k2 * n%:R.
  have [hA|hA] := leqP (2 * #|run [set v0] s1|) n.
    rewrite mulr1n.
    apply: le_trans (expList_le k2 (G := fun _ => 1) _) _.
      by move=> s2; case: (_ != _); rewrite ?mulr0n ?mulr1n ?ler01 ?lexx.
    by rewrite expList_const //; lra.
  rewrite mulr0n add0r.
  have -> : (fun s2 => (run [set v0] (s1 ++ s2) != [set: 'I_n])%:R : R)
      = fun s2 => (run (run [set v0] s1) s2 != [set: 'I_n])%:R.
    by apply/funext => s2; rewrite run_cat.
  have hpt s2 : (run (run [set v0] s1) s2 != [set: 'I_n])%:R
      <= n%:R - #|run (run [set v0] s1) s2|%:R :> R.
    have hc := card_run_le (run [set v0] s1) s2.
    rewrite -(ler_nat R) in hc.
    rewrite eqEcard finset.subsetT cardsT card_ord /= -ltnNge.
    have [h|h] := ltnP #|run (run [set v0] s1) s2| n.
      rewrite mulr1n lerBrDr -[X in X + _](mulr1n 1) -natrD ler_nat add1n.
      exact: h.
    by rewrite mulr0n; lra.
  apply: le_trans (expList_le k2 hpt) _.
  apply: le_trans (saturation k2 hn (ltnW hA)) _.
  apply: ler_wpM2l => //.
  by have := ler0n R #|run [set v0] s1|; lra.
apply: le_trans (expList_le k1 inner) _.
rewrite expListD expList_const //.
by have := phase1 v0 k1 hn hL; lra.
Qed.

(** Elementary log bounds from [one_sub_inv_le_ln] (Lean: [log_ge_198],
    [log_ge_1615], [log_ge_32]). *)
Lemma ln98_ge : 1 / 9 <= ln (9 / 8 : R).
Proof. by have := one_sub_inv_le_ln (x := 9 / 8 : R); lra. Qed.

Lemma ln1615_ge : 1 / 16 <= ln (16 / 15 : R).
Proof. by have := one_sub_inv_le_ln (x := 16 / 15 : R); lra. Qed.

Lemma ln32_ge : 1 / 3 <= ln (3 / 2 : R).
Proof. by have := one_sub_inv_le_ln (x := 3 / 2 : R); lra. Qed.

(** [ln 2 <= 7/10] (Lean uses [Real.log_two_lt_d9]); it is what makes the
    constants [9], [117], [23] of [numeric_B] work: [9 * 0.7 + 1 <= 117/16]. *)
Lemma ln2_le : ln (2 : R) <= 7 / 10.
Proof.
have x0 : 0 <= 7 / 10 :> R by lra.
have h : 2 <= expR (7 / 10 : R).
  have := expR_ge_series 4 x0.
  rewrite /series/= !big_nat_recr//= big_geq// /exp_coeff/= expr0 expr1.
  rewrite !factS fact0 !natrM !exprS expr0.
  by move=> h; lra.
by rewrite -(expRK (7 / 10 : R)) ler_ln ?posrE ?expR_gt0 //; lra.
Qed.

(** [ceiln] brackets for [x >= 0]: Lean's [Nat.le_ceil] and
    [Nat.ceil_lt_add_one]. *)
Lemma ceiln_ge (x : R) : 0 <= x -> x <= (ceiln x)%:R.
Proof.
move=> x0; rewrite /ceiln natr_absz ger0_norm ?ceil_ge //.
by rewrite ceil_ge0; lra.
Qed.

Lemma ceiln_lt (x : R) : 0 <= x -> (ceiln x)%:R < x + 1.
Proof.
move=> x0; rewrite /ceiln natr_absz ger0_norm; last by rewrite ceil_ge0; lra.
by have := ceilB1_lt x; rewrite intrB mulr1z; lra.
Qed.

(** Numeric step A: [ceiln (9 ln n) + 1] good rounds multiply a single
    informed node past [n], since [(9/8) ^ that >= n]. (Lean: [numeric_A].) *)
Lemma numeric_A :
  (2 <= n)%N -> n%:R <= (9 / 8 : R) ^+ (ceiln (9 * ln (n%:R : R)) + 1).
Proof.
move=> hn.
have n1 : 1 < n%:R :> R by rewrite ltr1n.
have hn' : n%:R = expR (ln (n%:R : R)) by rewrite lnK ?posrE //; lra.
set L := ln (n%:R : R) in hn' *.
have L0 : 0 < L by rewrite /L ln_gt0.
have hc : 9 * L <= (ceiln (9 * L))%:R by apply: ceiln_ge; lra.
have h98 := ln98_ge.
have -> : (9 / 8 : R) ^+ (ceiln (9 * L) + 1)
    = expR ((ceiln (9 * L) + 1)%:R * ln (9 / 8)).
  by rewrite expRM_natl lnK ?posrE //; lra.
rewrite hn' ler_expR natrD.
have := ler_pM (x1 := 9 * L) (x2 := 1 / 9) (y1 := (ceiln (9 * L))%:R)
  (y2 := ln (9 / 8)) _ _ hc h98; rewrite mulr1n.
by lra.
Qed.

(** Numeric step B: the growth-phase failure bound
    [2 ^ (ceiln (9 ln n) + 1) * (15/16) ^ (ceiln (117 ln n) + 23)] is at most
    [1/n]. (Lean: [numeric_B].) *)
Lemma numeric_B :
  (2 <= n)%N ->
  2 ^+ (ceiln (9 * ln (n%:R : R)) + 1) * (15 / 16 : R) ^+ (ceiln (117 * ln (n%:R : R)) + 23)
    <= 1 / n%:R.
Proof.
move=> hn.
have n1 : 1 < n%:R :> R by rewrite ltr1n.
have hn' : n%:R = expR (ln (n%:R : R)) by rewrite lnK ?posrE //; lra.
set L := ln (n%:R : R) in hn' *.
have L0 : 0 < L by rewrite /L ln_gt0.
have ha : (ceiln (9 * L))%:R < 9 * L + 1 by apply: ceiln_lt; lra.
have hb : 117 * L <= (ceiln (117 * L))%:R by apply: ceiln_ge; lra.
have h1615 := ln1615_ge.
have hln2 := ln2_le.
have ln2_0 : 0 <= ln (2 : R) by rewrite ln_ge0 //; lra.
have -> : 2 ^+ (ceiln (9 * L) + 1)
    = expR ((ceiln (9 * L) + 1)%:R * ln (2 : R)).
  by rewrite expRM_natl lnK ?posrE //; lra.
have -> : (15 / 16 : R) ^+ (ceiln (117 * L) + 23)
    = expR ((ceiln (117 * L) + 23)%:R * ln (15 / 16 : R)).
  by rewrite expRM_natl lnK ?posrE //; lra.
have -> : 1 / n%:R = expR (- L) by rewrite expRN -hn' div1r.
have -> : ln (15 / 16 : R) = - ln (16 / 15 : R).
  by rewrite !ln_div ?posrE ?ltr0n //; lra.
rewrite -expRD ler_expR !natrD.
have := ler_pM (x1 := (ceiln (9 * L))%:R + 1) (x2 := ln (2 : R))
  (y1 := 9 * L + 2) (y2 := 7 / 10) _ ln2_0 _ hln2.
have := ler_pM (x1 := 117 * L + 23) (x2 := 1 / 16)
  (y1 := (ceiln (117 * L))%:R + 23%:R) (y2 := ln (16 / 15 : R)) _ _ _ h1615.
rewrite mulr1n.
have := ler0n R (ceiln (9 * L)).
have := ler0n R (ceiln (117 * L)).
by lra.
Qed.

(** Numeric step C: [ceiln (6 ln n)] saturation rounds bring the expected
    number of uninformed nodes from [n] below [1/n]. (Lean: [numeric_C].) *)
Lemma numeric_C :
  (2 <= n)%N -> (2 / 3 : R) ^+ ceiln (6 * ln (n%:R : R)) * n%:R <= 1 / n%:R.
Proof.
move=> hn.
have n1 : 1 < n%:R :> R by rewrite ltr1n.
have hn' : n%:R = expR (ln (n%:R : R)) by rewrite lnK ?posrE //; lra.
set L := ln (n%:R : R) in hn' *.
have L0 : 0 < L by rewrite /L ln_gt0.
have hc : 6 * L <= (ceiln (6 * L))%:R by apply: ceiln_ge; lra.
have h32 := ln32_ge.
have -> : (2 / 3 : R) ^+ ceiln (6 * L)
    = expR ((ceiln (6 * L))%:R * ln (2 / 3 : R)).
  by rewrite expRM_natl lnK ?posrE //; lra.
have -> : ln (2 / 3 : R) = - ln (3 / 2 : R).
  by rewrite !ln_div ?posrE ?ltr0n //; lra.
have -> : 1 / n%:R = expR (- L) by rewrite expRN -hn' div1r.
rewrite [X in _ * X <= _]hn' -expRD ler_expR.
have := ler_pM (x1 := 6 * L) (x2 := 1 / 3) (y1 := (ceiln (6 * L))%:R)
  (y2 := ln (3 / 2 : R)) _ _ hc h32.
by lra.
Qed.

(** The main theorem. (Lean: [push_informs_all_whp].) *)
Theorem push_informs_all_whp (v0 : 'I_n) :
  (2 <= n)%N ->
  prNotAllInformed v0 ((ceiln (117 * ln (n%:R : R)) + 23) + ceiln (6 * ln (n%:R : R)))
    <= 2 / n%:R.
Proof.
move=> hn.
have hB := numeric_B hn; have hC := numeric_C hn.
apply: le_trans (prNotAllInformed_le v0 _ _ hn (numeric_A hn)) _.
lra.
Qed.

(** The same, as a lower bound on the probability that everyone is informed.
    (Lean: [push_informs_all_whp'].) *)
Theorem push_informs_all_whp' (v0 : 'I_n) :
  (2 <= n)%N ->
  1 - 2 / n%:R
    <= expList ((ceiln (117 * ln (n%:R : R)) + 23) + ceiln (6 * ln (n%:R : R)))
         (fun s : seq (Tgt n) => (run [set v0] s == [set: 'I_n])%:R : R).
Proof.
move=> hn.
have T0 := tgt_gt0 hn.
have hfail := push_informs_all_whp v0 hn.
set T := ((ceiln (117 * ln (n%:R : R)) + 23) + ceiln (6 * ln (n%:R : R)))%N in hfail *.
have hsum :
    expList T (fun s : seq (Tgt n) => (run [set v0] s == [set: 'I_n])%:R : R)
    + prNotAllInformed v0 T = 1.
  rewrite /prNotAllInformed -expListD -[RHS](expList_const T (1 : R) T0).
  congr expList; apply/funext => s.
  by case: (run [set v0] s == _); rewrite ?mulr0n ?mulr1n ?addr0 ?add0r.
lra.
Qed.

End Main.
