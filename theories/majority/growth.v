(** * Dynamics.majority.growth — the growth phase

    Port of [ThreeMajority/Growth.lean]. While the opinion-[1] fraction is in
    [[3/5, 3/4]] the majority map amplifies the bias by at least [5/4] per
    round in expectation; [10] rounds take the fraction past [3/4] except
    with probability at most [10 exp(-n / 10^7)]. Each round needs genuine
    concentration ([Dynamics.prob.chernoff]), because the opinion count is
    not monotone in the round index. *)

From Dynamics Require Import prelude.
From Dynamics.prob Require Import avg indep bounds chernoff.
From Dynamics.majority Require Import model oneround.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Growth.
Variable n : nat.
Context {R : realType}.
Implicit Types (I : {set 'I_n}).

(** Lean: [growthBias j = (1/10) (11/10)^j] — the bias schedule. *)
Definition growthBias (j : nat) : R := 1 / 10 * (11 / 10) ^+ j.

(** Lean: [growthBias_zero]. *)
Lemma growthBias0 : growthBias 0 = 1 / 10.
Proof. by rewrite /growthBias expr0 mulr1. Qed.

(** Lean: [growthBias_nonneg]. *)
Lemma growthBias_ge0 j : 0 <= growthBias j.
Proof. by rewrite /growthBias mulr_ge0 ?exprn_ge0 //; lra. Qed.

(** Lean: [growthBias_mono]. *)
Lemma growthBias_leS j : growthBias j <= growthBias j.+1.
Proof.
rewrite /growthBias exprS.
by have := exprn_ge0 j (_ : 0 <= 11 / 10 :> R); nra.
Qed.

(** Lean: [growthBias_le_of_le]. *)
Lemma growthBias_le i j : (i <= j)%N -> growthBias i <= growthBias j.
Proof. by move=> ij; rewrite /growthBias ler_pM2l ?ler_eXn2l //; lra. Qed.

(** Lean: [growthBias_le_quarter]. *)
Lemma growthBias_le_quarter j : (j <= 9)%N -> growthBias j <= 1 / 4.
Proof.
by case: j => [|[|[|[|[|[|[|[|[|[|j]]]]]]]]]] // _; rewrite /growthBias; lra.
Qed.

(** Lean: [growthBias_ten]. *)
Lemma growthBias10 : 1 / 4 < growthBias 10.
Proof. by rewrite /growthBias; lra. Qed.

(** Lean: [growth_round] — a single growth round amplifies the bias [β] by
    [11/10] except with probability [exp(-n / 10^7)]. *)
Lemma growth_round I (b : R) :
  (1 <= n)%N -> 1 / 10 <= b -> b <= 1 / 4 -> n%:R * (1 / 2 + b) <= #|I|%:R ->
  avg (fun r : Tgt3 n =>
         ((#|step I r|%:R <= n%:R * (1 / 2 + 11 / 10 * b))%R)%:R : R)
    <= expR (- (1 / 10 ^+ 7) * n%:R).
Proof.
move=> n1 b0 b1 hI; have n0 : (0 : R) < n%:R by rewrite ltr0n.
pose x : R := avg (ind I); have xE : x = #|I|%:R / n%:R := avg_indE I.
have cardle : #|I|%:R <= n%:R :> R.
  by rewrite ler_nat -[X in (_ <= X)%N](card_ord n) max_card.
have hx0 : 1 / 2 + b <= x by rewrite xE ler_pdivlMr // mulrC.
have hx1 : x <= 1 by rewrite xE ler_pdivrMr // mul1r.
set a := 1 / 2 + 11 / 10 * b; set c := 1 / 2 + 5 / 4 * b.
have c0 : 0 < c by rewrite /c; lra.
(* the mean is at least [n (1/2 + 5/4 b)]: [p(x) >= p(1/2 + b)] by
   monotonicity of [p(x) = 3x^2 - 2x^3] on [[0, 1]], then [p(1/2 + b)
   >= 1/2 + 5/4 b] since [b (1/4 - 2 b^2) >= 0] *)
have hmu : n%:R * c <= \sum_(v < n) avg (Y_maj I v).
  rewrite sum_avg_Y_maj // -/x ler_pM2l //.
  have hbase : c <= 3 * (1 / 2 + b) ^+ 2 - 2 * (1 / 2 + b) ^+ 3.
    have : 0 <= b * (1 / 4 - 2 * b ^+ 2) by apply: mulr_ge0; nra.
    by rewrite /c; lra.
  apply: le_trans hbase _; set y := 1 / 2 + b.
  have h1 : 0 <= (x - y) * x * (1 - y).
    by apply: mulr_ge0; [apply: mulr_ge0|]; rewrite /y; lra.
  have h2 : 0 <= (x - y) * y * (1 - x).
    by apply: mulr_ge0; [apply: mulr_ge0|]; rewrite /y; lra.
  have h3 : 0 <= (x - y) * x * (1 - x).
    by apply: mulr_ge0; [apply: mulr_ge0|]; rewrite /y; lra.
  have h4 : 0 <= (x - y) * y * (1 - y).
    by apply: mulr_ge0; [apply: mulr_ge0|]; rewrite /y; lra.
  lra.
have hk0 : 0 < n%:R * a by rewrite /a; nra.
have hkm : n%:R * a <= n%:R * c by rewrite /a /c; nra.
have hbound := avg_tail_le_ln_ge (Y_maj01 I) hmu hk0 hkm.
have -> : (fun r : Tgt3 n => ((#|step I r|%:R <= n%:R * a)%R)%:R : R)
    = fun r : Tgt3 n => ((\sum_(i < n) Y_maj I i (r i) <= n%:R * a)%R)%:R : R.
  by apply/funext => r; rewrite card_step_eq_sum.
apply: le_trans hbound _; rewrite ler_expR.
have -> : n%:R * a / (n%:R * c) = a / c.
  by rewrite -mulf_div divff ?mul1r // gt_eqF.
(* with [d := 1 - a/c] the exponent is exactly [- n c d^3] *)
set d := 1 - a / c.
have dE : d * c = c - a by rewrite /d mulrBl mul1r divfK // gt_eqF.
have rho12 : 1 / 2 <= a / c by rewrite ler_pdivlMr // /a /c; lra.
have rho1 : a / c <= 1 by rewrite ler_pdivrMr // mul1r /a /c; lra.
have hlogk := ler_wpM2l (ltW hk0) (ln_ge_quadratic rho12 rho1).
have d_lb : 1 / 55 <= d by rewrite -(ler_pM2r c0) dE /a /c; lra.
have d3 : (1 / 55) ^+ 3 <= d ^+ 3 by rewrite ler_pXn2r // nnegrE; lra.
have cd3 : 5 / 8 * (1 / 55) ^+ 3 <= c * d ^+ 3.
  by apply: ler_pM => //; rewrite ?exprn_ge0 // /c; lra.
have rhoE : a / c = 1 - d by rewrite /d; lra.
clearbody a c d.
have E : n%:R * a - n%:R * c - n%:R * a * ((a / c - 1) - (a / c - 1) ^+ 2)
    = - (n%:R * (c * d ^+ 3)).
  have aE : a = (1 - d) * c by rewrite mulrBl mul1r dE; lra.
  by rewrite rhoE aE; ring.
by have := ler_wpM2l (ltW n0) cd3; lra.
Qed.

(** Lean: [growth_fail_le] — union bound over [j] growth rounds. *)
Lemma growth_fail_le j :
  (1 <= n)%N -> forall i, (i + j <= 10)%N -> forall I,
  n%:R * (1 / 2 + growthBias i) <= #|I|%:R ->
  expList j (fun s : seq (Tgt3 n) =>
     ((n%:R * (1 / 2 + growthBias (i + j)) <= #|run I s|%:R)%R == false)%:R : R)
    <= j%:R * expR (- (1 / 10 ^+ 7) * n%:R).
Proof.
move=> n1; elim: j => [|j IH] i hij I hI.
  by rewrite addn0 /= hI mul0r.
have hb0 : 1 / 10 <= growthBias i by rewrite -growthBias0 growthBias_le.
have hb1 : growthBias i <= 1 / 4 by apply: growthBias_le_quarter; lia.
have gBS : 11 / 10 * growthBias i = growthBias i.+1.
  by rewrite /growthBias exprS mulrCA.
have hgrowth := growth_round n1 hb0 hb1 hI; rewrite gBS in hgrowth.
(* conditioning on the first round [r]: either it reaches the next
   threshold and the induction hypothesis applies to [step I r], or the
   failure indicator of the first round is [1] *)
have key (r : Tgt3 n) :
  expList j (fun s => ((n%:R * (1 / 2 + growthBias (i + j.+1))
                       <= #|run I (r :: s)|%:R)%R == false)%:R : R)
    <= ((#|step I r|%:R <= n%:R * (1 / 2 + growthBias i.+1))%R)%:R
       + j%:R * expR (- (1 / 10 ^+ 7) * n%:R).
  case: (leP (n%:R * (1 / 2 + growthBias i.+1)) #|step I r|%:R) => hcase.
    have hij' : (i.+1 + j <= 10)%N by lia.
    have := IH i.+1 hij' (step I r) hcase; rewrite addSnnS => /le_trans.
    by apply; rewrite lerDr ler0n.
  rewrite (ltW hcase) /= mulr1n.
  apply: (@le_trans _ _ (1 : R)).
    rewrite -[leRHS](expList_const j 1 (tgt3_gt0 n1)).
    apply: expList_le => s.
    by case: (_ == false); rewrite ?mulr1n ?mulr0n ?ler01.
  by rewrite lerDl mulr_ge0 ?ler0n ?expR_ge0.
apply: le_trans (avg_le key) _; rewrite avgD avg_const ?tgt3_gt0 //.
by rewrite -[j.+1%:R]natr1; lra.
Qed.

(** Lean: [growth_phase1] — from a [3/5] majority, [10] rounds reach a [3/4]
    majority except with probability [10 exp(-n / 10^7)]. *)
Lemma growth_phase1 (I0 : {set 'I_n}) :
  (1 <= n)%N -> n%:R * (3 / 5) <= #|I0|%:R :> R ->
  expList 10 (fun s : seq (Tgt3 n) =>
     ((n%:R * (3 / 4) <= #|run I0 s|%:R :> R) == false)%:R : R)
    <= 10 * expR (- (1 / 10 ^+ 7) * n%:R).
Proof.
move=> n1 hI0; have n0 : (0 : R) < n%:R by rewrite ltr0n.
have hI0' : n%:R * (1 / 2 + growthBias 0) <= #|I0|%:R.
  by rewrite growthBias0; lra.
have h := @growth_fail_le 10 n1 0 isT I0 hI0'.
apply: le_trans _ h; apply: expList_le => s /=.
case: (leP (n%:R * (3 / 4)) #|run I0 s|%:R) => h1 /=; first by rewrite ler0n.
case: (leP (n%:R * (1 / 2 + growthBias 10)) #|run I0 s|%:R) => h2 //=.
by have := growthBias10; nra.
Qed.

End Growth.
