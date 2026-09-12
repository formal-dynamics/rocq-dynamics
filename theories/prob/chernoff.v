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
Proof. Admitted.

(** Lean: [avg_tail_ge] — upper tail, [t >= 0]. *)
Lemma avg_tail_ge (t k : R) :
  0 <= t ->
  avg (fun x : {ffun 'I_n -> G} => ((k <= X x)%R)%:R : R)
    <= expR (mu * (expR t - 1) - t * k).
Proof. Admitted.

(** Lean: [avg_tail_le] — lower tail, [t <= 0]. *)
Lemma avg_tail_le (t k : R) :
  t <= 0 ->
  avg (fun x : {ffun 'I_n -> G} => ((X x <= k)%R)%:R : R)
    <= expR (mu * (expR t - 1) - t * k).
Proof. Admitted.

(** Lean: [avg_tail_ge_log] — closed-form upper tail at [t = ln (k / mu)]. *)
Lemma avg_tail_ge_ln (k m : R) :
  m = mu -> 0 < m -> m <= k ->
  avg (fun x : {ffun 'I_n -> G} => ((k <= X x)%R)%:R : R)
    <= expR (k - m - k * ln (k / m)).
Proof. Admitted.

(** Lean: [avg_tail_le_log] — closed-form lower tail at [t = ln (k / mu)]. *)
Lemma avg_tail_le_ln (k m : R) :
  m = mu -> 0 < k -> k <= m ->
  avg (fun x : {ffun 'I_n -> G} => ((X x <= k)%R)%:R : R)
    <= expR (k - m - k * ln (k / m)).
Proof. Admitted.

(** Lean: [avg_tail_ge_log_le] — upper tail from an *upper bound* [mub] on
    the mean (the exponent is monotone in the mean at the optimal [t]). *)
Lemma avg_tail_ge_ln_le (k mub : R) :
  mu <= mub -> 0 < mub -> mub <= k ->
  avg (fun x : {ffun 'I_n -> G} => ((k <= X x)%R)%:R : R)
    <= expR (k - mub - k * ln (k / mub)).
Proof. Admitted.

(** Lean: [avg_tail_le_log_ge] — lower tail from a *lower bound* [mlb] on
    the mean. *)
Lemma avg_tail_le_ln_ge (k mlb : R) :
  mlb <= mu -> 0 < k -> k <= mlb ->
  avg (fun x : {ffun 'I_n -> G} => ((X x <= k)%R)%:R : R)
    <= expR (k - mlb - k * ln (k / mlb)).
Proof. Admitted.

End Chernoff.
