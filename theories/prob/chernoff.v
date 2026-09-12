(** * Dynamics.prob.chernoff — an elementary Chernoff bound

    Port of [ThreeMajority/Chernoff.lean]. The only concentration tool of the
    development, proved from the single inequality [1 + x <= expR x]
    ([expR_ge1Dx]) plus independence ([avg_prod_ffun]):

    - [avg_exp_le] — the moment-generating-function bound for a sum of
      independent [{0,1}]-valued trials, [E[exp(tX)] <= exp(mu (e^t - 1))],
      for every real [t].
    - [avg_tail_ge] / [avg_tail_le] — the tail bounds obtained via Markov's
      inequality applied to [exp(t X)], for [t >= 0] / [t <= 0].
    - [avg_tail_ge_ln] / [avg_tail_le_ln] — the closed forms at the optimal
      [t = ln (k / mu)], and their versions assuming only a bound on the mean.

    Setting: [n] agents, agent [i]'s private randomness is [x i : G], its
    contribution is [Y i (x i) \in {0,1}], the sum is over the product space
    [{ffun 'I_n -> G}] and [mu = \sum_i avg (Y i)] is the mean. Indicators of
    events are written [(P)%:R]. *)

From Dynamics Require Import prelude.
From Dynamics.prob Require Import avg indep.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.


Section Chernoff.
Context {R : realType} {n : nat} {G : finType}.
Variable Y : 'I_n -> G -> R.
Hypothesis Y01 : forall i x, Y i x = 0 \/ Y i x = 1.

Local Notation X x := (\sum_(i < n) Y i (x i)).
Local Notation mu := (\sum_(i < n) avg (Y i)).

(** Lean: [avg_exp_le] — MGF bound, no sign restriction on [t]. *)
Lemma avg_exp_le (t : R) :
  avg (fun x : {ffun 'I_n -> G} => expR (t * X x)) <= expR (mu * (expR t - 1)).
Proof.
have -> : avg (fun x : {ffun 'I_n -> G} => expR (t * X x))
    = \prod_(i < n) avg (fun y => expR (t * Y i y)).
  rewrite -(avg_prod_ffun (fun i y => expR (t * Y i y))); congr avg.
  by apply/funext => x; rewrite mulr_sumr expR_sum.
rewrite mulr_suml expR_sum; apply: ler_prod => i _; apply/andP; split.
  by apply: avg_ge0 => y; exact: expR_ge0.
have -> : avg (fun y => expR (t * Y i y))
    = avg (fun y => 1 + (expR t - 1) * Y i y).
  congr avg; apply/funext => y.
  by case: (Y01 i y) => ->; rewrite ?mulr0 ?mulr1 ?expR0; lra.
case: (posnP #|G|) => [G0|G0].
  by rewrite /avg G0 mulr0n invr0 !mulr0 expR_ge0.
by rewrite avgD avg_const // avgZ [avg _ * _]mulrC expR_ge1Dx.
Qed.

(** Lean: [avg_tail_ge] — upper tail, [t >= 0]. *)
Lemma avg_tail_ge (t k : R) :
  0 <= t ->
  avg (fun x : {ffun 'I_n -> G} => ((k <= X x)%R)%:R : R)
    <= expR (mu * (expR t - 1) - t * k).
Proof.
move=> t0.
have pt (x : {ffun 'I_n -> G}) :
  (((k <= X x)%R)%:R : R) <= expR (- (t * k)) * expR (t * X x).
  rewrite -expRD; case: (leP k (X x)) => [kX|Xk].
    by rewrite mulr1n -[leLHS]expR0 ler_expR; nra.
  by rewrite mulr0n expR_ge0.
apply: le_trans (avg_le pt) _; rewrite avgZ -(addrC (- (t * k))) expRD.
by rewrite ler_pM2l ?expR_gt0 // avg_exp_le.
Qed.

(** Lean: [avg_tail_le] — lower tail, [t <= 0]. *)
Lemma avg_tail_le (t k : R) :
  t <= 0 ->
  avg (fun x : {ffun 'I_n -> G} => ((X x <= k)%R)%:R : R)
    <= expR (mu * (expR t - 1) - t * k).
Proof.
move=> t0.
have pt (x : {ffun 'I_n -> G}) :
  (((X x <= k)%R)%:R : R) <= expR (- (t * k)) * expR (t * X x).
  rewrite -expRD; case: (leP (X x) k) => [Xk|kX].
    by rewrite mulr1n -[leLHS]expR0 ler_expR; nra.
  by rewrite mulr0n expR_ge0.
apply: le_trans (avg_le pt) _; rewrite avgZ -(addrC (- (t * k))) expRD.
by rewrite ler_pM2l ?expR_gt0 // avg_exp_le.
Qed.

(** Lean: [avg_tail_ge_log] — closed-form upper tail at [t = ln (k / mu)]. *)
Lemma avg_tail_ge_ln (k m : R) :
  m = mu -> 0 < m -> m <= k ->
  avg (fun x : {ffun 'I_n -> G} => ((k <= X x)%R)%:R : R)
    <= expR (k - m - k * ln (k / m)).
Proof.
move=> mmu m0 mk; have k0 : 0 < k := lt_le_trans m0 mk.
have t0 : 0 <= ln (k / m) by apply: ln_ge0; rewrite ler_pdivlMr // mul1r.
apply: le_trans (avg_tail_ge k t0) _.
rewrite -mmu lnK ?posrE ?divr_gt0 // ler_expR.
have -> : m * (k / m - 1) = k - m.
  by rewrite mulrBr mulr1 mulrCA divff ?mulr1 // gt_eqF.
by lra.
Qed.

(** Lean: [avg_tail_le_log] — closed-form lower tail at [t = ln (k / mu)]. *)
Lemma avg_tail_le_ln (k m : R) :
  m = mu -> 0 < k -> k <= m ->
  avg (fun x : {ffun 'I_n -> G} => ((X x <= k)%R)%:R : R)
    <= expR (k - m - k * ln (k / m)).
Proof.
move=> mmu k0 km; have m0 : 0 < m := lt_le_trans k0 km.
have t0 : ln (k / m) <= 0 by apply: ln_le0; rewrite ler_pdivrMr // mul1r.
apply: le_trans (avg_tail_le k t0) _.
rewrite -mmu lnK ?posrE ?divr_gt0 // ler_expR.
have -> : m * (k / m - 1) = k - m.
  by rewrite mulrBr mulr1 mulrCA divff ?mulr1 // gt_eqF.
by lra.
Qed.

(** Lean: [avg_tail_ge_log_le] — upper tail from an *upper bound* [mub] on
    the mean (the exponent is monotone in the mean at the optimal [t]). *)
Lemma avg_tail_ge_ln_le (k mub : R) :
  mu <= mub -> 0 < mub -> mub <= k ->
  avg (fun x : {ffun 'I_n -> G} => ((k <= X x)%R)%:R : R)
    <= expR (k - mub - k * ln (k / mub)).
Proof.
move=> mu_ub mub0 mk; have k0 : 0 < k := lt_le_trans mub0 mk.
have t0 : 0 <= ln (k / mub) by apply: ln_ge0; rewrite ler_pdivlMr // mul1r.
apply: le_trans (avg_tail_ge k t0) _.
rewrite lnK ?posrE ?divr_gt0 // ler_expR.
have slope : 0 <= k / mub - 1 by rewrite subr_ge0 ler_pdivlMr // mul1r.
have mono := ler_wpM2r slope mu_ub.
have E : mub * (k / mub - 1) = k - mub.
  by rewrite mulrBr mulr1 mulrCA divff ?mulr1 // gt_eqF.
by lra.
Qed.

(** Lean: [avg_tail_le_log_ge] — lower tail from a *lower bound* [mlb] on
    the mean. *)
Lemma avg_tail_le_ln_ge (k mlb : R) :
  mlb <= mu -> 0 < k -> k <= mlb ->
  avg (fun x : {ffun 'I_n -> G} => ((X x <= k)%R)%:R : R)
    <= expR (k - mlb - k * ln (k / mlb)).
Proof.
move=> mu_lb k0 km; have mlb0 : 0 < mlb := lt_le_trans k0 km.
have t0 : ln (k / mlb) <= 0 by apply: ln_le0; rewrite ler_pdivrMr // mul1r.
apply: le_trans (avg_tail_le k t0) _.
rewrite lnK ?posrE ?divr_gt0 // ler_expR.
have slope : k / mlb - 1 <= 0 by rewrite subr_le0 ler_pdivrMr // mul1r.
have mono := ler_wnM2r slope mu_lb.
have E : mlb * (k / mlb - 1) = k - mlb.
  by rewrite mulrBr mulr1 mulrCA divff ?mulr1 // gt_eqF.
by lra.
Qed.

End Chernoff.
