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
Proof. Admitted.

(** Lean: [growthBias_nonneg]. *)
Lemma growthBias_ge0 j : 0 <= growthBias j.
Proof. Admitted.

(** Lean: [growthBias_mono]. *)
Lemma growthBias_leS j : growthBias j <= growthBias j.+1.
Proof. Admitted.

(** Lean: [growthBias_le_of_le]. *)
Lemma growthBias_le i j : (i <= j)%N -> growthBias i <= growthBias j.
Proof. Admitted.

(** Lean: [growthBias_le_quarter]. *)
Lemma growthBias_le_quarter j : (j <= 9)%N -> growthBias j <= 1 / 4.
Proof. Admitted.

(** Lean: [growthBias_ten]. *)
Lemma growthBias10 : 1 / 4 < growthBias 10.
Proof. Admitted.

(** Lean: [growth_round] — a single growth round amplifies the bias [β] by
    [11/10] except with probability [exp(-n / 10^7)]. *)
Lemma growth_round I (b : R) :
  (1 <= n)%N -> 1 / 10 <= b -> b <= 1 / 4 -> n%:R * (1 / 2 + b) <= #|I|%:R ->
  avg (fun r : Tgt3 n =>
         ((#|step I r|%:R <= n%:R * (1 / 2 + 11 / 10 * b))%R)%:R : R)
    <= expR (- (1 / 10 ^+ 7) * n%:R).
Proof. Admitted.

(** Lean: [growth_fail_le] — union bound over [j] growth rounds. *)
Lemma growth_fail_le j :
  (1 <= n)%N -> forall i, (i + j <= 10)%N -> forall I,
  n%:R * (1 / 2 + growthBias i) <= #|I|%:R ->
  expList j (fun s : seq (Tgt3 n) =>
     ((n%:R * (1 / 2 + growthBias (i + j)) <= #|run I s|%:R)%R == false)%:R : R)
    <= j%:R * expR (- (1 / 10 ^+ 7) * n%:R).
Proof. Admitted.

(** Lean: [growth_phase1] — from a [3/5] majority, [10] rounds reach a [3/4]
    majority except with probability [10 exp(-n / 10^7)]. *)
Lemma growth_phase1 (I0 : {set 'I_n}) :
  (1 <= n)%N -> n%:R * (3 / 5) <= #|I0|%:R :> R ->
  expList 10 (fun s : seq (Tgt3 n) =>
     ((n%:R * (3 / 4) <= #|run I0 s|%:R :> R) == false)%:R : R)
    <= 10 * expR (- (1 / 10 ^+ 7) * n%:R).
Proof. Admitted.

End Growth.
