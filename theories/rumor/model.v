(** * Dynamics.rumor.model — the uniform push protocol on the complete graph

    Port of [RumorSpread/Model.lean] (Lean namespace [RumorPush]).

    - [Tgt n] — a round configuration: every node [v] picks a target
      [u != v]. It is a dependent finite function, so it is a [finType] with
      [#|Tgt n| = (n - 1) ^ n] ([Dynamics.rumor.oneround.card_tgt]).
    - [step I r] — one round: the informed set [I] plus the targets of its
      members (uninformed nodes also draw a target, which is ignored; this is
      the formalization-friendly convention of the Lean development).
    - [run I s] — the informed set after consuming the list [s] of rounds.
    - [goodRound], [goodCount] — a round is good if it grows the informed set
      by a factor [9/8] or if the informed set already exceeds [n/2]; the
      deterministic growth lemma [pow_goodCount_mul_card_le_card_run] says
      that below half-saturation each good round did multiply the size by
      [9/8]. *)

From Dynamics Require Import prelude.
From Dynamics.prob Require Import avg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Lean: [Tgt n := ∀ v : Fin n, {u : Fin n // u ≠ v}]. *)
Notation Tgt n := {dffun forall v : 'I_n, {u : 'I_n | u != v}}.

(** Lean: [tgt_nonempty]. *)
Lemma tgt_gt0 (n : nat) : (2 <= n)%N -> (0 < #|Tgt n|)%N.
Proof. Admitted.

Section Model.
Variable n : nat.
Implicit Types (I : {set 'I_n}) (r : Tgt n) (s : seq (Tgt n)) (u v : 'I_n).

(** Lean: [step I r = I ∪ I.image (fun v => (r v : Fin n))]. *)
Definition step I r : {set 'I_n} := I :|: [set val (r v) | v in I].

(** Lean: [subset_step]. *)
Lemma subset_step I r : I \subset step I r.
Proof. Admitted.

(** Lean: [card_le_card_step]. *)
Lemma card_le_card_step I r : (#|I| <= #|step I r|)%N.
Proof. Admitted.

(** Lean: [card_step_le] — a round at most doubles the informed set. *)
Lemma card_step_le I r : (#|step I r| <= 2 * #|I|)%N.
Proof. Admitted.

(** Lean: [mem_step]. *)
Lemma mem_step I r u :
  reflect (u \in I \/ exists2 v, v \in I & val (r v) = u) (u \in step I r).
Proof. Admitted.

(** Lean: [run I l] — fold [step] over a list of rounds. *)
Fixpoint run I s : {set 'I_n} :=
  if s is r :: s' then run (step I r) s' else I.

(** Lean: [run_nil]. *)
Lemma run_nil I : run I [::] = I.
Proof. Admitted.

(** Lean: [run_cons]. *)
Lemma run_cons I r s : run I (r :: s) = run (step I r) s.
Proof. Admitted.

(** Lean: [subset_run] — the informed set only grows. *)
Lemma subset_run I s : I \subset run I s.
Proof. Admitted.

(** Lean: [run_append]. *)
Lemma run_cat I s1 s2 : run I (s1 ++ s2) = run (run I s1) s2.
Proof. Admitted.

(** Lean: [card_run_le]. *)
Lemma card_run_le I s : (#|run I s| <= n)%N.
Proof. Admitted.

(** Lean: [goodRound] — the round grew [I] by a factor [9/8], or [I] already
    exceeds [n/2]. Decidable in Lean, a [bool] here. *)
Definition goodRound I r : bool :=
  (9 * #|I| <= 8 * #|step I r|)%N || (n < 2 * #|I|)%N.

(** Lean: [goodCount] — number of good rounds along a trajectory. *)
Fixpoint goodCount I s : nat :=
  if s is r :: s' then goodRound I r + goodCount (step I r) s' else 0.

(** Lean: [goodCount_nil]. *)
Lemma goodCount_nil I : goodCount I [::] = 0%N.
Proof. Admitted.

(** Lean: [goodCount_cons]. *)
Lemma goodCount_cons I r s :
  goodCount I (r :: s) = (goodRound I r + goodCount (step I r) s)%N.
Proof. Admitted.

(** Lean: [pow_goodCount_mul_card_le_card_run] — as long as the final
    informed set is still [<= n/2], each good round multiplied its size by
    [9/8]. *)
Lemma pow_goodCount_mul_card_le_card_run (R : realType) I s :
  (2 * #|run I s| <= n)%N ->
  (9 / 8 : R) ^+ goodCount I s * #|I|%:R <= #|run I s|%:R.
Proof. Admitted.

End Model.
