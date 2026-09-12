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
Proof. by rewrite /ind; case: (x \in I); [right | left]. Qed.

(** Lean: [avg_ind]. *)
Lemma avg_ind I : avg (ind I) = #|I|%:R / #|'I_n|%:R.
Proof. by rewrite /ind (avg_ind (fun x => x \in I)). Qed.

(** Lean: [avg_ind_eq]. *)
Lemma avg_indE I : avg (ind I) = #|I|%:R / n%:R.
Proof. by rewrite avg_ind card_ord. Qed.

(** Lean: [majorityIndicator_eq] — majority of three as a polynomial. *)
Lemma majorityIndicatorE I t :
  ((2 <= sampleCountOf I t)%N)%:R
    = ind I t.1 * ind I t.2.1 + ind I t.2.1 * ind I t.2.2
        + ind I t.1 * ind I t.2.2 - 2 * (ind I t.1 * ind I t.2.1 * ind I t.2.2).
Proof.
rewrite /sampleCountOf /ind.
by case: (t.1 \in I); case: (t.2.1 \in I); case: (t.2.2 \in I);
  rewrite /= ?mulr0n ?mulr1n; lra.
Qed.

(** Lean: [avg_ind_mul_fst_snd1]. *)
Lemma avg_ind_mul_fst_snd1 I :
  (0 < n)%N ->
  avg (fun t : 'I_n * ('I_n * 'I_n) => ind I t.1 * ind I t.2.1)
    = avg (ind I) * avg (ind I).
Proof.
move=> n0.
rewrite (avg_mul_prod (ind I) (fun q : 'I_n * 'I_n => ind I q.1)).
by rewrite avg_fst // card_ord.
Qed.

(** Lean: [avg_ind_mul_snd1_snd2]. *)
Lemma avg_ind_mul_snd1_snd2 I :
  (0 < n)%N ->
  avg (fun t : 'I_n * ('I_n * 'I_n) => ind I t.2.1 * ind I t.2.2)
    = avg (ind I) * avg (ind I).
Proof.
move=> n0.
rewrite (avg_snd (fun q : 'I_n * 'I_n => ind I q.1 * ind I q.2)) ?card_ord //.
exact: avg_mul_prod.
Qed.

(** Lean: [avg_ind_mul_fst_snd2]. *)
Lemma avg_ind_mul_fst_snd2 I :
  (0 < n)%N ->
  avg (fun t : 'I_n * ('I_n * 'I_n) => ind I t.1 * ind I t.2.2)
    = avg (ind I) * avg (ind I).
Proof.
move=> n0.
rewrite (avg_mul_prod (ind I) (fun q : 'I_n * 'I_n => ind I q.2)).
by rewrite avg_snd // card_ord.
Qed.

(** Lean: [avg_ind_mul_triple]. *)
Lemma avg_ind_mul_triple I :
  (0 < n)%N ->
  avg (fun t : 'I_n * ('I_n * 'I_n) => ind I t.1 * ind I t.2.1 * ind I t.2.2)
    = avg (ind I) * avg (ind I) * avg (ind I).
Proof.
move=> _.
have -> : (fun t : 'I_n * ('I_n * 'I_n) =>
    ind I t.1 * ind I t.2.1 * ind I t.2.2)
  = fun t => ind I t.1 * (ind I t.2.1 * ind I t.2.2).
  by apply/funext => t; rewrite mulrA.
rewrite (avg_mul_prod (ind I) (fun q : 'I_n * 'I_n => ind I q.1 * ind I q.2)).
by rewrite avg_mul_prod mulrA.
Qed.

(** Lean: [Y_maj I v s] — agent [v]'s contribution to the next opinion-[1]
    count when its samples are [s] (the agent index is unused). *)
Definition Y_maj I (v : 'I_n) t : R := ((2 <= sampleCountOf I t)%N)%:R.

(** Lean: [Y_maj_zero_one]. *)
Lemma Y_maj01 I v t : Y_maj I v t = 0 \/ Y_maj I v t = 1.
Proof. by rewrite /Y_maj; case: (_ <= _)%N; [right | left]. Qed.

(** Lean: [card_step_eq_sum]. *)
Lemma card_step_eq_sum I r :
  #|step I r|%:R = \sum_(v < n) Y_maj I v (r v) :> R.
Proof.
rewrite /Y_maj -sum1_card natr_sum big_mkcond /=; apply: eq_bigr => v _.
by rewrite mem_step /sampleCount; case: (_ <= _)%N.
Qed.

(** Lean: [avg_Y_maj_eq]. *)
Lemma avg_Y_majE I v :
  (0 < n)%N ->
  avg (Y_maj I v)
    = avg (ind I) * avg (ind I) * 3 - 2 * (avg (ind I) * avg (ind I) * avg (ind I)).
Proof.
move=> n0.
have -> : Y_maj I v = fun t =>
    ind I t.1 * ind I t.2.1 + ind I t.2.1 * ind I t.2.2
    + ind I t.1 * ind I t.2.2 - 2 * (ind I t.1 * ind I t.2.1 * ind I t.2.2).
  by apply/funext => t; exact: majorityIndicatorE.
rewrite avgB !avgD avgZ avg_ind_mul_fst_snd1 // avg_ind_mul_snd1_snd2 //.
by rewrite avg_ind_mul_fst_snd2 // avg_ind_mul_triple //; ring.
Qed.

(** Lean: [sum_avg_Y_maj]. *)
Lemma sum_avg_Y_maj I :
  (1 <= n)%N ->
  \sum_(v < n) avg (Y_maj I v)
    = n%:R * (3 * avg (ind I) ^+ 2 - 2 * avg (ind I) ^+ 3).
Proof.
move=> n0; rewrite (eq_bigr (fun _ => avg (ind I) * avg (ind I) * 3
    - 2 * (avg (ind I) * avg (ind I) * avg (ind I)))) => [|v _]; last first.
  exact: avg_Y_majE.
by rewrite sumr_const card_ord -mulr_natl; ring.
Qed.

(** Lean: [avg_card_step] — the exact cubic drift. *)
Lemma avg_card_step I :
  (1 <= n)%N ->
  avg (fun r : Tgt3 n => #|step I r|%:R : R)
    = n%:R * (3 * avg (ind I) ^+ 2 - 2 * avg (ind I) ^+ 3).
Proof.
move=> n1; have n0 : (0 < n)%N := n1.
have -> : (fun r : Tgt3 n => #|step I r|%:R : R)
    = fun r => \sum_(v < n) Y_maj I v (r v).
  by apply/funext => r; exact: card_step_eq_sum.
rewrite avg_sum -(sum_avg_Y_maj I n1); apply: eq_bigr => v _.
by rewrite (avg_eval v (Y_maj I v)) // !card_prod !card_ord !muln_gt0 n0.
Qed.

(** Lean: [Y_dis I v s = 1 - Y_maj I v s] — the dissent contribution. *)
Definition Y_dis I v t : R := 1 - Y_maj I v t.

(** Lean: [Y_dis_zero_one]. *)
Lemma Y_dis01 I v t : Y_dis I v t = 0 \/ Y_dis I v t = 1.
Proof.
rewrite /Y_dis; case: (Y_maj01 I v t) => ->.
  by right; rewrite subr0.
by left; rewrite subrr.
Qed.

(** Lean: [card_dissent_eq_sum]. *)
Lemma card_dissent_eq_sum I r :
  n%:R - #|step I r|%:R = \sum_(v < n) Y_dis I v (r v) :> R.
Proof.
by rewrite /Y_dis sumrB sumr_const card_ord card_step_eq_sum.
Qed.

(** Lean: [sum_avg_Y_dis]. *)
Lemma sum_avg_Y_dis I :
  (1 <= n)%N ->
  \sum_(v < n) avg (Y_dis I v)
    = n%:R - n%:R * (3 * avg (ind I) ^+ 2 - 2 * avg (ind I) ^+ 3).
Proof.
move=> n1; have n0 : (0 < n)%N := n1.
rewrite (eq_bigr (fun v => 1 - avg (Y_maj I v))) => [|v _]; last first.
  by rewrite /Y_dis avgB avg_const // !card_prod !card_ord !muln_gt0 n0.
by rewrite sumrB sumr_const card_ord sum_avg_Y_maj.
Qed.

End OneRound.
