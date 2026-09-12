(** * Dynamics.majority.main — 3-majority reaches consensus in [O(log n)] rounds

    Port of [ThreeMajority/Main.lean]. Glues the growth phase to the three
    saturation stages through the [expList] conditioning idiom and states
    the main theorem with the same constants as Lean: if [ln n >= 30] and
    the initial opinion-[1] set has at least [(3/5) n] agents, then after
    [10 + (⌈6 ln n⌉ + 2)] rounds all agents hold opinion [1] with
    probability at least [1 - 500/n]. *)

From Dynamics Require Import prelude.
From Dynamics.prob Require Import avg indep bounds chernoff.
From Dynamics.majority Require Import model oneround growth saturation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Main.
Variable n : nat.
Context {R : realType}.
Implicit Types (I : {set 'I_n}).

(** Lean: [ne_univ_iff_pos_dissent]. *)
Lemma neq_setT_dissent I :
  (I != [set: 'I_n]) = (1 <= n%:R - #|I|%:R :> R).
Proof.
rewrite eqEcard finset.subsetT cardsT card_ord /= -ltnNge.
by rewrite lerBrDr -[X in X + _](mulr1n 1) -natrD ler_nat add1n.
Qed.

(** Lean: [hfloor4_of_hbig]. *)
Lemma floor4_of_big : 30 <= ln (n%:R : R) -> 500 * ln n%:R <= n%:R / 4 :> R.
Proof.
move=> hbig.
have n2 := two_le_of_ln_ge30 hbig.
have n0 : (0 : R) < n%:R by rewrite ltr0n; lia.
have hn : n%:R = expR (ln (n%:R : R)) by rewrite lnK ?posrE.
set L := ln (n%:R : R) in hbig hn *.
have L0 : 0 <= L by lra.
have h5 := expR_ge_pow 5 L0; rewrite -hn in h5.
have hL4 : (30 : R) ^+ 4 <= L ^+ 4 by rewrite ler_pXn2r ?nnegrE //; lra.
have e5 : L ^+ 5 = L ^+ 4 * L by rewrite exprSr.
rewrite !factS fact0 !natrM in h5; rewrite !exprS expr0 in hL4.
nra.
Qed.

(** Lean: [saturation_2b2c] — stages 2b and 2c combined. *)
Lemma saturation_2b2c I :
  30 <= ln (n%:R : R) -> n%:R - #|I|%:R <= 500 * ln n%:R :> R ->
  expList 2 (fun s : seq (Tgt3 n) => ((1 <= n%:R - #|run I s|%:R :> R))%:R : R)
    <= expR (- ln n%:R) + 300 / n%:R.
Proof.
move=> hbig hUI.
have n1 : (1 <= n)%N by have := two_le_of_ln_ge30 hbig; lia.
have T0 := tgt3_gt0 n1.
have n0 : (0 : R) < n%:R by rewrite ltr0n.
have key r1 :
    expList 1 (fun s => ((1 <= n%:R - #|run I (r1 :: s)|%:R :> R))%:R : R)
      <= ((10 <= n%:R - #|step I r1|%:R :> R))%:R + 300 / n%:R.
  rewrite expListS /=.
  have [h10|h10] := leP 10 (n%:R - #|step I r1|%:R); last first.
    rewrite mulr0n add0r.
    by have := saturation_stage2c (I := step I r1) n1 (ltW h10); apply.
  rewrite mulr1n.
  apply: le_trans (avg_le (g := fun _ => 1) _) _.
    by move=> a; case: (1 <= _); rewrite ?mulr0n ?mulr1n ?ler01 ?lexx.
  rewrite avg_const //.
  have : 0 <= 300 / n%:R :> R by apply: divr_ge0; rewrite ler0n.
  lra.
rewrite expListS.
apply: le_trans (avg_le key) _.
rewrite avgD avg_const //.
by have := saturation_stage2b hbig hUI; lra.
Qed.

(** Lean: [saturation_2a2b2c] — all three saturation stages combined. *)
Lemma saturation_2a2b2c (I0 : {set 'I_n}) :
  30 <= ln (n%:R : R) -> n%:R - #|I0|%:R <= n%:R / 4 :> R ->
  expList (T2a n R + 2)
    (fun s : seq (Tgt3 n) => ((1 <= n%:R - #|run I0 s|%:R :> R))%:R : R)
    <= (T2a n R)%:R * expR (- 2 * ln n%:R) + (expR (- ln n%:R) + 300 / n%:R).
Proof.
move=> hbig hI0.
have n2 := two_le_of_ln_ge30 hbig.
have n1 : (1 <= n)%N by lia.
have T0 := tgt3_gt0 n1.
have n0 : (0 : R) < n%:R by rewrite ltr0n.
have hfloor4 := floor4_of_big hbig.
have pos : 0 <= expR (- ln n%:R) + 300 / n%:R :> R.
  by apply: addr_ge0; [exact: expR_ge0 | apply: divr_ge0; rewrite ler0n].
rewrite expList_cat.
have inner s1 :
    expList 2 (fun s2 => ((1 <= n%:R - #|run I0 (s1 ++ s2)|%:R :> R))%:R : R)
      <= ((500 * ln n%:R < n%:R - #|run I0 s1|%:R :> R))%:R
         + (expR (- ln n%:R) + 300 / n%:R).
  have [hA|hA] := ltP (500 * ln n%:R) (n%:R - #|run I0 s1|%:R).
    rewrite mulr1n.
    apply: le_trans (expList_le 2 (G := fun _ => 1) _) _.
      by move=> s2; case: (1 <= _); rewrite ?mulr0n ?mulr1n ?ler01 ?lexx.
    by rewrite expList_const //; lra.
  rewrite mulr0n add0r.
  have -> : (fun s2 => ((1 <= n%:R - #|run I0 (s1 ++ s2)|%:R :> R))%:R : R)
      = fun s2 => ((1 <= n%:R - #|run (run I0 s1) s2|%:R :> R))%:R.
    by apply/funext => s2; rewrite run_cat.
  exact: saturation_2b2c hbig hA.
apply: le_trans (expList_le _ inner) _.
rewrite expListD expList_const //.
by have := saturation_stage2a n2 hfloor4 hI0; lra.
Qed.

(** Lean: [majority3_consensus_fail_le] — main failure bound, raw form. *)
Theorem majority3_consensus_fail_le (I0 : {set 'I_n}) :
  30 <= ln (n%:R : R) -> n%:R * (3 / 5) <= #|I0|%:R :> R ->
  expList (10 + (T2a n R + 2))
    (fun s : seq (Tgt3 n) => ((1 <= n%:R - #|run I0 s|%:R :> R))%:R : R)
    <= 10 * expR (- (1 / 10 ^+ 7) * n%:R)
       + ((T2a n R)%:R * expR (- 2 * ln n%:R)
          + (expR (- ln n%:R) + 300 / n%:R)).
Proof.
move=> hbig hI0.
have n1 : (1 <= n)%N by have := two_le_of_ln_ge30 hbig; lia.
have T0 := tgt3_gt0 n1.
have n0 : (0 : R) < n%:R by rewrite ltr0n.
set B : R := (T2a n R)%:R * expR (- 2 * ln n%:R) + (expR (- ln n%:R) + 300 / n%:R).
have B0 : 0 <= B.
  rewrite /B; apply: addr_ge0; first by apply: mulr_ge0; rewrite ?ler0n ?expR_ge0.
  by apply: addr_ge0; [exact: expR_ge0 | apply: divr_ge0; rewrite ler0n].
rewrite expList_cat.
have inner s1 :
    expList (T2a n R + 2)
      (fun s2 => ((1 <= n%:R - #|run I0 (s1 ++ s2)|%:R :> R))%:R : R)
      <= ((n%:R * (3 / 4) <= #|run I0 s1|%:R :> R) == false)%:R + B.
  have [hA|hA] := leP (n%:R * (3 / 4)) (#|run I0 s1|%:R).
    rewrite /= mulr0n add0r.
    have -> : (fun s2 => ((1 <= n%:R - #|run I0 (s1 ++ s2)|%:R :> R))%:R : R)
        = fun s2 => ((1 <= n%:R - #|run (run I0 s1) s2|%:R :> R))%:R.
      by apply/funext => s2; rewrite run_cat.
    by apply: saturation_2a2b2c hbig _; lra.
  rewrite /= mulr1n.
  apply: le_trans (expList_le _ (G := fun _ => 1) _) _.
    by move=> s2; case: (1 <= _); rewrite ?mulr0n ?mulr1n ?ler01 ?lexx.
  by rewrite expList_const //; lra.
apply: le_trans (expList_le _ inner) _.
rewrite expListD expList_const //.
by have := growth_phase1 n1 hI0; lra.
Qed.

(** Lean: [majority3_consensus_fail_le_clean] — clean numeric bound. *)
Theorem majority3_consensus_fail_le_clean (I0 : {set 'I_n}) :
  30 <= ln (n%:R : R) -> n%:R * (3 / 5) <= #|I0|%:R :> R ->
  expList (10 + (T2a n R + 2))
    (fun s : seq (Tgt3 n) => ((1 <= n%:R - #|run I0 s|%:R :> R))%:R : R)
    <= 500 / n%:R.
Proof.
move=> hbig hI0.
have n2 := two_le_of_ln_ge30 hbig.
have n1 : (1 <= n)%N by lia.
have n0 : (0 : R) < n%:R by rewrite ltr0n.
have hfloor4 := floor4_of_big hbig.
apply: le_trans (majority3_consensus_fail_le hbig hI0) _.
have hn : n%:R = expR (ln (n%:R : R)) by rewrite lnK ?posrE.
rewrite /T2a /ceiln.
set L := ln (n%:R : R) in hbig hfloor4 hn *.
have L0 : 0 <= L by lra.
(* n is large: n >= L^14 / 14! >= 30^14 / 14! >= 5 * 10^9 *)
have hnbig : 5 * 10 ^+ 9 <= n%:R :> R.
  have h14 := expR_ge_pow 14 L0; rewrite -hn in h14.
  have hL14 : (30 : R) ^+ 14 <= L ^+ 14 by rewrite ler_pXn2r ?nnegrE //; lra.
  rewrite !factS fact0 !natrM in h14; rewrite !exprS expr0 in hL14 *.
  lra.
(* term 1: 10 exp(-n/10^7) <= 1/n *)
have hterm1 : 10 * expR (- (1 / 10 ^+ 7) * n%:R) <= 1 / n%:R :> R.
  pose x : R := (1 / 10 ^+ 7) * n%:R.
  have -> : - (1 / 10 ^+ 7) * n%:R = - x :> R by rewrite /x mulNr.
  have hx : 500 <= x by rewrite /x !exprS expr0 in hnbig *; lra.
  have x0 : 0 <= x by lra.
  have e5 := expR_ge_pow 5 x0; rewrite !factS fact0 !natrM in e5.
  have hx4 : (500 : R) ^+ 4 <= x ^+ 4 by rewrite ler_pXn2r ?nnegrE //; lra.
  have e : x ^+ 5 = x ^+ 4 * x by rewrite exprSr.
  have hnx : n%:R = 10 ^+ 7 * x.
    by rewrite /x mulrA mul1r mulfV ?mul1r // gt_eqF // exprn_gt0.
  have hkey : 10 * n%:R <= expR x.
    by rewrite !exprS expr0 in hx4 hnx; nra.
  rewrite expRN ler_pdivrMr ?expR_gt0 // div1r [X in _ <= X]mulrC.
  by rewrite ler_pdivlMr.
(* term 2: T2a exp(-2 ln n) = T2a / n^2 <= 1/n *)
have hterm2 : `|Num.ceil (6 * L)|%:R * expR (- 2 * L) <= 1 / n%:R.
  have hc : `|Num.ceil (6 * L)|%:R <= 6 * L + 1 :> R.
    rewrite natr_absz ger0_norm ?ceil_ge0; last by lra.
    by have := ceilB1_lt (6 * L); rewrite intrB mulr1z; lra.
  have hT : `|Num.ceil (6 * L)|%:R <= n%:R :> R by lra.
  rewrite mulNr expRN expRM_natl -hn expr2 invfM mulrA -[leRHS]mul1r div1r.
  apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
  by rewrite ler_pdivrMr // mul1r.
(* term 3: exp(-ln n) = 1/n *)
have hterm3 : expR (- L) = 1 / n%:R by rewrite expRN -hn div1r.
have : 0 <= 1 / n%:R :> R by apply: divr_ge0; rewrite ?ler01 ?ler0n.
rewrite hterm3; lra.
Qed.

(** Lean: [majority3_consensus_whp] — the main theorem. *)
Theorem majority3_consensus_whp (I0 : {set 'I_n}) :
  30 <= ln (n%:R : R) -> n%:R * (3 / 5) <= #|I0|%:R :> R ->
  1 - 500 / n%:R
    <= expList (10 + (T2a n R + 2))
         (fun s : seq (Tgt3 n) => (run I0 s == [set: 'I_n])%:R : R).
Proof.
move=> hbig hI0.
have n1 : (1 <= n)%N by have := two_le_of_ln_ge30 hbig; lia.
have T0 := tgt3_gt0 n1.
have hfail := majority3_consensus_fail_le_clean hbig hI0.
have hsum :
    expList (10 + (T2a n R + 2))
      (fun s : seq (Tgt3 n) => (run I0 s == [set: 'I_n])%:R : R)
    + expList (10 + (T2a n R + 2))
        (fun s => ((1 <= n%:R - #|run I0 s|%:R :> R))%:R : R) = 1.
  rewrite -expListD -[RHS](expList_const (10 + (T2a n R + 2)) (1 : R) T0).
  congr expList; apply/funext => s; rewrite -neq_setT_dissent.
  by case: (run I0 s == _); rewrite ?mulr0n ?mulr1n ?addr0 ?add0r.
lra.
Qed.

End Main.
