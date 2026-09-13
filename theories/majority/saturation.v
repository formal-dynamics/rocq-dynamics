(** * Dynamics.majority.saturation — the saturation phase

    Port of [ThreeMajority/Saturation.lean]. Three stages take the dissent
    count [U = n - |I|] from at most [n/4] to exactly [0]: a geometric
    descent by [7/10] per round over [T2a n = ⌈6 ln n⌉] rounds down to the
    floor [500 ln n] (stage 2a), one round from that floor to the constant
    [10] (stage 2b), and one Markov step to [0] (stage 2c). The per-round
    bounds are the mean-scaled Chernoff bounds of [Dynamics.prob.chernoff]
    applied to the dissent decomposition [Y_dis]. *)

From Dynamics Require Import prelude.
From mathcomp.analysis Require Import normedtype derive.
From Dynamics.prob Require Import avg indep bounds chernoff.
From Dynamics.majority Require Import model oneround.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** ** The Padé lower bound on [ln]

    Mathlib's [Real.le_log_one_add_of_nonneg] ([2x/(x+2) <= ln (1+x)]) has no
    MathComp-Analysis counterpart; it is the one place where the *upper* tail
    needs a cubically tight bound on [ln], so it is proved here from the mean
    value theorem: [g t = t (e^t + 1) - 2 (e^t - 1)] vanishes at [0] and has
    derivative [1 + (t - 1) e^t >= 0], which is [1 + x <= e^x] at [-t]. *)
Section Pade.
Context {R : realType}.
(* section-local: makes [R] a normed module over itself for [is_derive] *)
Import numFieldNormedType.Exports.

(** [2 (e^t - 1) <= t (e^t + 1)] for [t >= 0]. *)
Lemma expR_pade (t : R) : 0 <= t -> 2 * (expR t - 1) <= t * (expR t + 1).
Proof.
move=> t0.
pose g : R -> R := fun s => s * (expR s + 1) - 2 * (expR s - 1).
pose dg : R -> R := fun s => 1 + (s - 1) * expR s.
have hdg (x : R) : is_derive x (1 : R) g (dg x).
  rewrite /g /dg; apply: is_derive_eq.
  by rewrite /GRing.scale /= addr0 subr0 mulr1; ring.
have dg0 (x : R) : 0 <= dg x.
  have := expR_ge1Dx (- x).
  by rewrite /dg expRN -div1r ler_pdivlMr ?expR_gt0 //; lra.
have [c _ E] : exists2 c, c \in `[0, t] & g t - g 0 = dg c * (t - 0).
  apply: MVT_segment => //.
  by apply: derivable_within_continuous => x _; case: (hdg x).
have := mulr_ge0 (dg0 c) t0.
by move: E; rewrite /g /= expR0 => E; lra.
Qed.

(** Padé-type lower bound on [ln]: for [1 <= x], [2 (x - 1) <= ln x (x + 1)].
    This is what turns the Chernoff exponent into the quadratic form used by
    [saturation_round_numeric]. (Lean: [Real.le_log_one_add_of_nonneg],
    multiplied out.) *)
Lemma ln_ge_pade (x : R) : 1 <= x -> 2 * (x - 1) <= ln x * (x + 1).
Proof.
move=> x1; have x0 : 0 < x by lra.
by have := expR_pade (t := ln x) (ln_ge0 x1); rewrite lnK ?posrE.
Qed.

End Pade.

Section Saturation.
Variable n : nat.
Context {R : realType}.
Implicit Types (I : {set 'I_n}).

(** Per-round upper tail from an upper bound on the mean dissent. (Lean:
    [saturation_round_generic].) *)
Lemma saturation_round_generic I (mub k : R) :
  (1 <= n)%N -> 0 < mub -> mub <= k -> \sum_(v < n) avg (Y_dis I v) <= mub ->
  avg (fun r : Tgt3 n => ((k <= n%:R - #|step I r|%:R :> R))%:R : R)
    <= expR (k - mub - k * ln (k / mub)).
Proof.
move=> n1 mub0 hk hmu.
have hbound := avg_tail_ge_ln_le (Y_dis01 I) hmu mub0 hk.
have -> : (fun r : Tgt3 n => ((k <= n%:R - #|step I r|%:R :> R))%:R : R)
    = fun r : Tgt3 n => ((k <= \sum_(i < n) Y_dis I i (r i))%R)%:R : R.
  by apply/funext => r; rewrite card_dissent_eq_sum.
exact: hbound.
Qed.

(** Closed-form per-round upper tail. (Lean: [saturation_round_closed].) *)
Lemma saturation_round_closed I (M k : R) :
  (1 <= n)%N -> 0 < M -> M <= n%:R / 4 -> 5 / 8 * M <= k ->
  n%:R - #|I|%:R <= M ->
  avg (fun r : Tgt3 n => ((k <= n%:R - #|step I r|%:R :> R))%:R : R)
    <= expR (k - 5 / 8 * M - k * ln (k / (5 / 8 * M))).
Proof.
move=> n1 M0 M1 hkM hUI; have n0 : (0 : R) < n%:R by rewrite ltr0n.
have mub0 : 0 < 5 / 8 * M by lra.
apply: (saturation_round_generic n1 mub0 hkM).
pose x : R := avg (ind I); have xE : x = #|I|%:R / n%:R := avg_indE I.
have hnx : n%:R * x = #|I|%:R by rewrite xE mulrCA divff ?mulr1 // gt_eqF.
have cardle : #|I|%:R <= n%:R :> R.
  by rewrite ler_nat -[X in (_ <= X)%N](card_ord n) max_card.
have hx1 : x <= 1 by rewrite xE ler_pdivrMr // mul1r.
have hx34 : 3 / 4 <= x by rewrite -(ler_pM2l n0); lra.
rewrite sum_avg_Y_dis // -/x.
(* [n - n p(x) = n (1 - x) (1 - x) (1 + 2x)] and [(1 - x)(1 + 2x) <= 5/8]
   on [[3/4, 1]] *)
have -> : n%:R - n%:R * (3 * x ^+ 2 - 2 * x ^+ 3)
    = n%:R * (1 - x) * ((1 - x) * (1 + 2 * x)) by ring.
have hU0 : 0 <= n%:R * (1 - x) by apply: mulr_ge0; lra.
have hq : (1 - x) * (1 + 2 * x) <= 5 / 8 by nra.
by have := ler_wpM2l hU0 hq; lra.
Qed.

(** The mean dissent is at most [3 M^2 / n]. (Lean: [saturation_mean_quad].) *)
Lemma saturation_mean_quad I (M : R) :
  (1 <= n)%N -> 0 <= M -> n%:R - #|I|%:R <= M ->
  \sum_(v < n) avg (Y_dis I v) <= 3 * M ^+ 2 / n%:R.
Proof.
move=> n1 M0 hUI; have n0 : (0 : R) < n%:R by rewrite ltr0n.
pose x : R := avg (ind I); have xE : x = #|I|%:R / n%:R := avg_indE I.
have hnx : n%:R * x = #|I|%:R by rewrite xE mulrCA divff ?mulr1 // gt_eqF.
have cardle : #|I|%:R <= n%:R :> R.
  by rewrite ler_nat -[X in (_ <= X)%N](card_ord n) max_card.
have hx1 : x <= 1 by rewrite xE ler_pdivrMr // mul1r.
rewrite sum_avg_Y_dis // -/x ler_pdivlMr //.
(* with [U := n (1 - x) <= M]: [n (n - n p(x)) = U^2 (1 + 2x) <= 3 U^2] *)
have -> : (n%:R - n%:R * (3 * x ^+ 2 - 2 * x ^+ 3)) * n%:R
    = (n%:R * (1 - x)) ^+ 2 * (1 + 2 * x) by ring.
have hU0 : 0 <= n%:R * (1 - x) by apply: mulr_ge0; lra.
have hUM : n%:R * (1 - x) <= M by lra.
have hU2 : (n%:R * (1 - x)) ^+ 2 <= M ^+ 2 by rewrite ler_pXn2r ?nnegrE.
by have := sqr_ge0 (n%:R * (1 - x)); nra.
Qed.

(** The same tail with the exponent put in the usable quadratic form
    [-(k - 5M/8)^2 / (k + 5M/8)]. (Lean: [saturation_round_numeric].) *)
Lemma saturation_round_numeric I (M k : R) :
  (1 <= n)%N -> 0 < M -> M <= n%:R / 4 -> 5 / 8 * M <= k -> 0 < k ->
  n%:R - #|I|%:R <= M ->
  avg (fun r : Tgt3 n => ((k <= n%:R - #|step I r|%:R :> R))%:R : R)
    <= expR (- (k - 5 / 8 * M) ^+ 2 / (k + 5 / 8 * M)).
Proof.
move=> n1 M0 M1 hkM k0 hUI.
apply: le_trans (saturation_round_closed n1 M0 M1 hkM hUI) _.
rewrite ler_expR; set m := 5 / 8 * M in hkM *.
have m0 : 0 < m by rewrite /m; lra.
clearbody m; have km0 : 0 < k + m by lra.
have r1 : 1 <= k / m by rewrite ler_pdivlMr // mul1r.
(* Padé: [2 (k - m) <= (k + m) ln (k / m)] *)
have h1 : 2 * (k - m) <= ln (k / m) * (k + m).
  have := ler_wpM2r (ltW m0) (ln_ge_pade r1).
  have E : k / m * m = k by rewrite divfK // gt_eqF.
  have E2 : ln (k / m) * (k / m) * m = ln (k / m) * k by rewrite -mulrA E.
  by lra.
have h2 := ler_wpM2l (ltW k0) h1.
by rewrite ler_pdivlMr //; lra.
Qed.

(** Dissent contracts by [7/10] except with probability [exp(-M / 250)]. (Lean:
    [saturation_round_contract].) *)
Lemma saturation_round_contract I (M : R) :
  (1 <= n)%N -> 0 < M -> M <= n%:R / 4 -> n%:R - #|I|%:R <= M ->
  avg (fun r : Tgt3 n => ((7 / 10 * M <= n%:R - #|step I r|%:R :> R))%:R : R)
    <= expR (- (1 / 250) * M).
Proof.
move=> n1 M0 M1 hUI.
have hk0 : 0 < 7 / 10 * M by lra.
have hkM : 5 / 8 * M <= 7 / 10 * M by lra.
apply: le_trans (saturation_round_numeric n1 M0 M1 hkM hk0 hUI) _.
rewrite ler_expR ler_pdivrMr; last by lra.
by nra.
Qed.

(** The deterministic dissent target after [i] rounds. (Lean: [satAfter n M i =
    max (500 ln n) ((7/10)^i M)].) *)
Definition satAfter (M : R) (i : nat) : R :=
  Num.max (500 * ln n%:R) ((7 / 10) ^+ i * M).

(** The dissent target never drops below its floor [500 ln n].
    (Lean: [satAfter_ge_floor].) *)
Lemma satAfter_ge_floor M i : 500 * ln n%:R <= satAfter M i.
Proof. by rewrite /satAfter le_max lexx. Qed.

(** Above the floor, the schedule starts at [M].
    (Lean: [satAfter_zero].) *)
Lemma satAfter0 M : 500 * ln n%:R <= M -> satAfter M 0 = M.
Proof. by move=> h; rewrite /satAfter expr0 mul1r max_r. Qed.

(** The schedule stays below [n/4], the range in which the per-round
    contraction applies. (Lean: [satAfter_le_of_le].) *)
Lemma satAfter_le M i :
  0 <= M -> M <= n%:R / 4 -> 500 * ln n%:R <= n%:R / 4 :> R ->
  satAfter M i <= n%:R / 4.
Proof.
move=> M0 M1 hfloor4; rewrite /satAfter ge_max hfloor4 /=.
apply: le_trans _ M1; rewrite -[leRHS]mul1r.
by apply: ler_wpM2r => //; apply: exprn_ile1; lra.
Qed.

(** One step of the schedule contracts by at most [7/10], matching the
    per-round contraction. (Lean: [satAfter_contract_le].) *)
Lemma satAfter_contract_le M i :
  (1 <= n)%N -> 7 / 10 * satAfter M i <= satAfter M i.+1.
Proof.
move=> n1; have L0 : 0 <= ln n%:R :> R by rewrite ln_ge0 // ler1n.
rewrite /satAfter.
have -> : (7 / 10 : R) ^+ i.+1 * M = 7 / 10 * ((7 / 10) ^+ i * M).
  by rewrite exprS mulrA.
rewrite maxr_pMr; last by lra.
by rewrite ge_max !le_max lexx orbT andbT; apply/orP; left; lra.
Qed.

(** Stage 2a, union bound. (Lean: [saturation_fail_le].) *)
Lemma saturation_fail_le (M : R) j :
  (2 <= n)%N -> 500 * ln n%:R <= M -> M <= n%:R / 4 ->
  500 * ln n%:R <= n%:R / 4 :> R ->
  forall i I, n%:R - #|I|%:R <= satAfter M i ->
  expList j (fun s : seq (Tgt3 n) =>
     ((satAfter M (i + j) < n%:R - #|run I s|%:R :> R))%:R : R)
    <= j%:R * expR (- 2 * ln n%:R).
Proof.
move=> n2 hM0 hM1 hfloor4.
have n1 : (1 <= n)%N by lia.
have T0 := tgt3_gt0 n1.
have L0 : 0 < ln n%:R :> R by rewrite ln_gt0 // ltr1n.
have M0 : 0 <= M by lra.
elim: j => [|j IH] i I hUI.
  by rewrite addn0 /= ltNge hUI /= mul0r.
rewrite expListS.
have hMi0 : 0 < satAfter M i by have := @satAfter_ge_floor M i; lra.
have hMi1 : satAfter M i <= n%:R / 4 := @satAfter_le M i M0 hM1 hfloor4.
have hsat := saturation_round_contract n1 hMi0 hMi1 hUI.
(* conditioning on the first round [r]: either the dissent already
   contracted by [7/10] and the induction hypothesis applies to [step I r],
   or the failure indicator of the first round is [1] *)
have key (r : Tgt3 n) :
  expList j (fun s =>
      ((satAfter M (i + j.+1) < n%:R - #|run I (r :: s)|%:R :> R))%:R : R)
    <= ((7 / 10 * satAfter M i <= n%:R - #|step I r|%:R :> R))%:R
       + j%:R * expR (- 2 * ln n%:R).
  case: (leP (7 / 10 * satAfter M i) (n%:R - #|step I r|%:R)) => hcase.
    rewrite mulr1n; apply: (@le_trans _ _ (1 : R)).
      rewrite -[leRHS](expList_const j 1 T0).
      apply: expList_le => s.
      by case: (_ < _); rewrite ?mulr1n ?mulr0n ?ler01.
    by rewrite lerDl mulr_ge0 ?ler0n ?expR_ge0.
  rewrite mulr0n add0r.
  have hle : n%:R - #|step I r|%:R <= satAfter M i.+1.
    exact: le_trans (ltW hcase) (@satAfter_contract_le M i n1).
  by have := IH i.+1 (step I r) hle; rewrite addSnnS.
apply: le_trans (avg_le key) _; rewrite avgD avg_const //.
have hle2 : expR (- (1 / 250) * satAfter M i) <= expR (- 2 * ln n%:R).
  by rewrite ler_expR; have := @satAfter_ge_floor M i; lra.
by rewrite -[j.+1%:R]natr1; lra.
Qed.

(** Length of saturation stage 2a: the number of contraction rounds needed to
    bring the dissent from [n/4] down to the floor.
    (Lean: [T2a n = ⌈6 log n⌉₊].) *)
Definition T2a : nat := ceiln (6 * ln (n%:R : R)).

(** [T2a] rounds of the schedule do take [n/4] down to the floor [500 ln n].
    (Lean: [satAfter_quarter_le_floor].) *)
Lemma satAfter_quarter_le_floor :
  (2 <= n)%N -> satAfter (n%:R / 4) T2a <= 500 * ln n%:R.
Proof.
move=> n2; have n0 : (0 : R) < n%:R by rewrite ltr0n; lia.
have L0 : 0 < ln n%:R :> R by rewrite ln_gt0 // ltr1n.
(* [ln n >= ln 2 >= 1/2] *)
have hL2 : 1 / 2 <= ln n%:R :> R.
  have h2 : 1 - 1 / 2 <= ln (2 : R) by apply: one_sub_inv_le_ln; lra.
  have h2n : ln (2 : R) <= ln n%:R.
    by rewrite ler_ln ?posrE // ?ler_nat // ltr0n.
  by lra.
have hn : n%:R = expR (ln (n%:R : R)) by rewrite lnK ?posrE.
have hT : 6 * ln n%:R <= T2a%:R :> R.
  rewrite /T2a /ceiln natr_absz ger0_norm ?ceil_ge0; last by lra.
  exact: ceil_ge.
set L := ln n%:R in L0 hL2 hn hT *.
rewrite /satAfter ge_max lexx /=.
have n40 : 0 <= n%:R / 4 :> R by rewrite divr_ge0 // ler0n.
(* [ln (7/10) <= -3/10], so [(7/10)^T2a <= exp (-(9/5) L) <= exp (-L)] *)
have h710 : ln (7 / 10 : R) <= - (3 / 10).
  have m1 : -1 < - (3 / 10) :> R by lra.
  by have := le_ln1Dx m1; rewrite (_ : 1 + - (3 / 10) = 7 / 10 :> R) //; lra.
have hpow : (7 / 10 : R) ^+ T2a <= expR (- L).
  have -> : (7 / 10 : R) ^+ T2a = expR (T2a%:R * ln (7 / 10)).
    by rewrite expRM_natl lnK ?posrE //; lra.
  rewrite ler_expR.
  have h1 : T2a%:R * ln (7 / 10 : R) <= 6 * L * ln (7 / 10).
    by apply: ler_wnM2r hT; lra.
  have h2 : 6 * L * ln (7 / 10 : R) <= 6 * L * (- (3 / 10)).
    by apply: ler_wpM2l h710; lra.
  by lra.
(* [lra] is slow with the non-numeral exponent [T2a] in scope: clear it *)
apply: le_trans (ler_wpM2r n40 hpow) _; clear hpow.
rewrite expRN -hn mulrA mulVf ?gt_eqF // mul1r.
by lra.
Qed.

(** Stage 2a: from a dissent of at most [n/4], after [T2a] rounds the dissent
    exceeds [500 ln n] with probability at most [T2a * n^(-2)].
    (Lean: [saturation_stage2a].) *)
Lemma saturation_stage2a (I0 : {set 'I_n}) :
  (2 <= n)%N -> 500 * ln n%:R <= n%:R / 4 :> R ->
  n%:R - #|I0|%:R <= n%:R / 4 :> R ->
  expList T2a (fun s : seq (Tgt3 n) =>
     ((500 * ln n%:R < n%:R - #|run I0 s|%:R :> R))%:R : R)
    <= T2a%:R * expR (- 2 * ln n%:R).
Proof.
move=> n2 hfloor4 hI0.
have h := @saturation_fail_le (n%:R / 4) T2a n2 hfloor4 (lexx _) hfloor4 0 I0.
rewrite add0n (satAfter0 hfloor4) in h.
apply: le_trans _ (h hI0); apply: expList_le => s.
have hle := satAfter_quarter_le_floor n2.
case: (ltP (500 * ln n%:R) (n%:R - #|run I0 s|%:R)) => hc.
  by rewrite (le_lt_trans hle hc).
by rewrite mulr0n ler0n.
Qed.

(** Stage 2b: from a dissent of at most [500 ln n], one round brings it below
    [10] except with probability [1/n]. (Lean: [saturation_stage2b].) *)
Lemma saturation_stage2b I :
  30 <= ln n%:R :> R -> n%:R - #|I|%:R <= 500 * ln n%:R :> R ->
  avg (fun r : Tgt3 n => ((10 <= n%:R - #|step I r|%:R :> R))%:R : R)
    <= expR (- ln n%:R).
Proof.
move=> hbig hUI.
have n2 := two_le_of_ln_ge30 hbig.
have n1 : (1 <= n)%N by lia.
have n0 : (0 : R) < n%:R by rewrite ltr0n.
have hn : n%:R = expR (ln (n%:R : R)) by rewrite lnK ?posrE.
have Lpos : 0 < ln (n%:R : R) by lra.
have hll := ln_ln_le Lpos.
set L := ln (n%:R : R) in hbig hUI hn Lpos hll *.
have L0 : 0 <= L by lra.
have M0 : 0 <= 500 * L by lra.
have hmu := saturation_mean_quad n1 M0 hUI.
set mub := 3 * (500 * L) ^+ 2 / n%:R in hmu.
have L2 : 0 < (500 * L) ^+ 2 by rewrite exprn_gt0 //; lra.
have nV0 : 0 < n%:R^-1 :> R by rewrite invr_gt0.
have mub0 : 0 < mub by rewrite /mub; nra.
(* [n = e^L >= L^11 / 11!] and [L >= 30] give [mub <= 9] *)
have hmub9 : mub <= 9.
  rewrite /mub ler_pdivrMr //.
  have h11 := expR_ge_pow 11 L0; rewrite -hn in h11.
  have hL9 : (30 : R) ^+ 9 <= L ^+ 9 by rewrite ler_pXn2r ?nnegrE //; lra.
  have h9 : 0 <= L ^+ 9 - 30 ^+ 9 by lra.
  have := mulr_ge0 (sqr_ge0 L) h9.
  rewrite !factS fact0 !natrM in h11; rewrite !exprS expr0 in hL9 *.
  by lra.
have hk : mub <= 10 by lra.
apply: le_trans (saturation_round_generic n1 mub0 hk hmu) _.
rewrite ler_expR.
(* [10 / mub = n / (75000 L^2) >= n / L^6] since [L^4 >= 30^4 > 75000], so
   [ln (10 / mub) >= L - 6 ln L]; the literal [75000] is avoided because
   [lra] converts large numerals unary *)
have hlog : L - 6 * ln L <= ln (10 / mub).
  have h6 : 3 * (500 * L) ^+ 2 <= 10 * L ^+ 6.
    have hL4 : (30 : R) ^+ 4 <= L ^+ 4 by rewrite ler_pXn2r ?nnegrE //; lra.
    have : 0 <= L ^+ 2 * (L ^+ 4 - 30 ^+ 4).
      by apply: mulr_ge0; [exact: sqr_ge0 | lra].
    by have := sqr_ge0 L; rewrite !exprS expr0 in hL4 *; lra.
  have L60 : 0 < L ^+ 6 by rewrite exprn_gt0.
  have hq : n%:R / L ^+ 6 <= 10 / mub.
    rewrite ler_pdivrMr // mulrAC ler_pdivlMr //.
    have -> : n%:R * mub = 3 * (500 * L) ^+ 2.
      by rewrite /mub mulrC divfK // gt_eqF.
    exact: h6.
  have -> : L - 6 * ln L = ln (n%:R / L ^+ 6).
    by rewrite ln_div ?posrE // lnXn // -/L -mulr_natr; lra.
  by rewrite ler_ln ?posrE // divr_gt0.
by lra.
Qed.

(** Stage 2c: from a dissent of at most [10], one round reaches full
    consensus except with probability [300/n].
    (Lean: [saturation_stage2c].) *)
Lemma saturation_stage2c I :
  (1 <= n)%N -> n%:R - #|I|%:R <= 10 :> R ->
  avg (fun r : Tgt3 n => ((1 <= n%:R - #|step I r|%:R :> R))%:R : R)
    <= 300 / n%:R.
Proof.
move=> n1 hUI; have n0 : (0 < n)%N := n1.
have h10 : 0 <= 10 :> R by lra.
have hmean := saturation_mean_quad n1 h10 hUI.
have e : 3 * 10 ^+ 2 = 300 :> R by rewrite expr2; ring.
rewrite e in hmean.
(* Markov: the indicator of [1 <= U] is at most [U] for integer [U >= 0] *)
apply: le_trans (avg_le (g := fun r => n%:R - #|step I r|%:R) _) _.
  move=> r; have hc : #|step I r|%:R <= n%:R :> R.
    by rewrite ler_nat card_step_le.
  case: (leP 1 (n%:R - #|step I r|%:R)) => h.
    by rewrite mulr1n.
  by rewrite mulr0n; lra.
have -> : (fun r : Tgt3 n => n%:R - #|step I r|%:R : R)
    = fun r => \sum_(v < n) Y_dis I v (r v).
  by apply/funext => r; exact: card_dissent_eq_sum.
rewrite avg_sum; apply: le_trans _ hmean; apply: ler_sum => v _.
by rewrite (avg_eval v (Y_dis I v)) // !card_prod !card_ord !muln_gt0 n0.
Qed.

End Saturation.

(* [T2a] has type [nat] but depends on [R] through [ln]; make [R] explicit so
   that [T2a n R] is well-formed outside the section. *)
Arguments T2a : clear implicits.
