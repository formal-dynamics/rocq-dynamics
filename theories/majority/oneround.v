(** * Dynamics.majority.oneround — the exact one-round drift

    Port of [ThreeMajority/OneRound.lean]. The cubic majority map
    [p(x) = 3x^2 - 2x^3] via the polynomial identity
    [maj(a,b,c) = ab + bc + ac - 2abc] on [{0,1}], plus the per-agent
    [{0,1}]-valued decompositions [Y_maj] / [Y_dis] of the opinion-[1] count
    and of the dissent count that the Chernoff bounds consume. *)

From Dynamics Require Import prelude.
From Dynamics.prob Require Import avg indep.
From Dynamics.majority Require Import model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section OneRound.
Variable n : nat.
Context {R : realType}.
Implicit Types (I : {set 'I_n}) (r : Tgt3 n) (v x : 'I_n)
  (t : 'I_n * ('I_n * 'I_n)).

(** Lean: [ind I x] — the real-valued indicator of [x ∈ I]. *)
Definition ind I x : R := (x \in I)%:R.

(** Lean: [ind_eq_zero_or_one]. *)
Lemma ind01 I x : ind I x = 0 \/ ind I x = 1.
Proof. Admitted.

(** Lean: [avg_ind]. *)
Lemma avg_ind I : avg (ind I) = #|I|%:R / #|'I_n|%:R.
Proof. Admitted.

(** Lean: [avg_ind_eq]. *)
Lemma avg_indE I : avg (ind I) = #|I|%:R / n%:R.
Proof. Admitted.

(** Lean: [majorityIndicator_eq] — majority of three as a polynomial. *)
Lemma majorityIndicatorE I t :
  ((2 <= sampleCountOf I t)%N)%:R
    = ind I t.1 * ind I t.2.1 + ind I t.2.1 * ind I t.2.2
        + ind I t.1 * ind I t.2.2 - 2 * (ind I t.1 * ind I t.2.1 * ind I t.2.2).
Proof. Admitted.

(** Lean: [avg_ind_mul_fst_snd1]. *)
Lemma avg_ind_mul_fst_snd1 I :
  (0 < n)%N ->
  avg (fun t : 'I_n * ('I_n * 'I_n) => ind I t.1 * ind I t.2.1)
    = avg (ind I) * avg (ind I).
Proof. Admitted.

(** Lean: [avg_ind_mul_snd1_snd2]. *)
Lemma avg_ind_mul_snd1_snd2 I :
  (0 < n)%N ->
  avg (fun t : 'I_n * ('I_n * 'I_n) => ind I t.2.1 * ind I t.2.2)
    = avg (ind I) * avg (ind I).
Proof. Admitted.

(** Lean: [avg_ind_mul_fst_snd2]. *)
Lemma avg_ind_mul_fst_snd2 I :
  (0 < n)%N ->
  avg (fun t : 'I_n * ('I_n * 'I_n) => ind I t.1 * ind I t.2.2)
    = avg (ind I) * avg (ind I).
Proof. Admitted.

(** Lean: [avg_ind_mul_triple]. *)
Lemma avg_ind_mul_triple I :
  (0 < n)%N ->
  avg (fun t : 'I_n * ('I_n * 'I_n) => ind I t.1 * ind I t.2.1 * ind I t.2.2)
    = avg (ind I) * avg (ind I) * avg (ind I).
Proof. Admitted.

(** Lean: [Y_maj I v s] — agent [v]'s contribution to the next opinion-[1]
    count when its samples are [s] (the agent index is unused). *)
Definition Y_maj I (v : 'I_n) t : R := ((2 <= sampleCountOf I t)%N)%:R.

(** Lean: [Y_maj_zero_one]. *)
Lemma Y_maj01 I v t : Y_maj I v t = 0 \/ Y_maj I v t = 1.
Proof. Admitted.

(** Lean: [card_step_eq_sum]. *)
Lemma card_step_eq_sum I r :
  #|step I r|%:R = \sum_(v < n) Y_maj I v (r v) :> R.
Proof. Admitted.

(** Lean: [avg_Y_maj_eq]. *)
Lemma avg_Y_majE I v :
  (0 < n)%N ->
  avg (Y_maj I v)
    = avg (ind I) * avg (ind I) * 3 - 2 * (avg (ind I) * avg (ind I) * avg (ind I)).
Proof. Admitted.

(** Lean: [sum_avg_Y_maj]. *)
Lemma sum_avg_Y_maj I :
  (1 <= n)%N ->
  \sum_(v < n) avg (Y_maj I v)
    = n%:R * (3 * avg (ind I) ^+ 2 - 2 * avg (ind I) ^+ 3).
Proof. Admitted.

(** Lean: [avg_card_step] — the exact cubic drift. *)
Lemma avg_card_step I :
  (1 <= n)%N ->
  avg (fun r : Tgt3 n => #|step I r|%:R : R)
    = n%:R * (3 * avg (ind I) ^+ 2 - 2 * avg (ind I) ^+ 3).
Proof. Admitted.

(** Lean: [Y_dis I v s = 1 - Y_maj I v s] — the dissent contribution. *)
Definition Y_dis I v t : R := 1 - Y_maj I v t.

(** Lean: [Y_dis_zero_one]. *)
Lemma Y_dis01 I v t : Y_dis I v t = 0 \/ Y_dis I v t = 1.
Proof. Admitted.

(** Lean: [card_dissent_eq_sum]. *)
Lemma card_dissent_eq_sum I r :
  n%:R - #|step I r|%:R = \sum_(v < n) Y_dis I v (r v) :> R.
Proof. Admitted.

(** Lean: [sum_avg_Y_dis]. *)
Lemma sum_avg_Y_dis I :
  (1 <= n)%N ->
  \sum_(v < n) avg (Y_dis I v)
    = n%:R - n%:R * (3 * avg (ind I) ^+ 2 - 2 * avg (ind I) ^+ 3).
Proof. Admitted.

End OneRound.
