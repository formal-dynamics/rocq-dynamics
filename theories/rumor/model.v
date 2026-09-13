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

(** A round configuration: every node [v] picks a target [u != v]. Being a
    dependent finite function it is itself a [finType], which is what makes a
    round a uniform draw from a finite space.
    (Lean: [Tgt n := ∀ v : Fin n, {u : Fin n // u ≠ v}].) *)
Notation Tgt n := {dffun forall v : 'I_n, {u : 'I_n | u != v}}.

(** There is at least one round configuration as soon as [n >= 2], so
    averaging over [Tgt n] is meaningful. (Lean: [tgt_nonempty].) *)
Lemma tgt_gt0 (n : nat) : (2 <= n)%N -> (0 < #|Tgt n|)%N.
Proof.
case: n => [|[|m]] // _; apply/card_gt0P.
have lt1 : (1 < m.+2)%N by [].
have neq0 (v : 'I_m.+2) : (if v == ord0 then Ordinal lt1 else ord0) != v.
  by case: ifP => [/eqP-> | ]; last rewrite eq_sym => ->.
by exists [ffun v => exist (fun u => u != v) _ (neq0 v)].
Qed.

Section Model.
Variable n : nat.
Implicit Types (I : {set 'I_n}) (r : Tgt n) (s : seq (Tgt n)) (u v : 'I_n).

(** One round: the informed set together with the targets of its members.
    Uninformed nodes also draw a target, which is ignored — the
    formalization-friendly convention of the Lean development.
    (Lean: [step I r = I ∪ I.image (fun v => (r v : Fin n))].) *)
Definition step I r : {set 'I_n} := I :|: [set val (r v) | v in I].

(** A round never un-informs a node. (Lean: [subset_step].) *)
Lemma subset_step I r : I \subset step I r.
Proof. exact: finset.subsetUl. Qed.

(** Hence the informed set never shrinks. (Lean: [card_le_card_step].) *)
Lemma card_le_card_step I r : (#|I| <= #|step I r|)%N.
Proof. exact: subset_leq_card (subset_step I r). Qed.

(** A round at most doubles the informed set. (Lean: [card_step_le].) *)
Lemma card_step_le I r : (#|step I r| <= 2 * #|I|)%N.
Proof.
rewrite /step cardsU mul2n -addnn; apply: leq_trans (leq_subr _ _) _.
by rewrite leq_add2l leq_imset_card.
Qed.

(** [u] is informed after a round exactly when it was already informed or is
    the target of some informed node. (Lean: [mem_step].) *)
Lemma mem_step I r u :
  reflect (u \in I \/ exists2 v, v \in I & val (r v) = u) (u \in step I r).
Proof.
apply: (iffP setUP) => [[uI | /imsetP[v vI ->]] | [uI | [v vI <-]]].
- by left.
- by right; exists v.
- by left.
- by right; apply: imset_f.
Qed.

(** Fold [step] over a list of rounds. (Lean: [run I l].) *)
Fixpoint run I s : {set 'I_n} :=
  if s is r :: s' then run (step I r) s' else I.

(** No rounds, no change. (Lean: [run_nil].) *)
Lemma run_nil I : run I [::] = I.
Proof. by []. Qed.

(** Peeling the first round off a trajectory. (Lean: [run_cons].) *)
Lemma run_cons I r s : run I (r :: s) = run (step I r) s.
Proof. by []. Qed.

(** The informed set only grows. (Lean: [subset_run].) *)
Lemma subset_run I s : I \subset run I s.
Proof.
elim: s I => [|r s IH] I /=; first exact: subxx.
exact: fintype.subset_trans (subset_step I r) (IH _).
Qed.

(** Running a concatenation of round lists is running one list after the
    other — the trajectory counterpart of [expList_cat], used to split the
    growth and saturation phases. (Lean: [run_append].) *)
Lemma run_cat I s1 s2 : run I (s1 ++ s2) = run (run I s1) s2.
Proof. by elim: s1 I => [|r s1 IH] I //=. Qed.

(** The informed set never exceeds all [n] nodes. (Lean: [card_run_le].) *)
Lemma card_run_le I s : (#|run I s| <= n)%N.
Proof. by rewrite -[leqRHS](card_ord n) max_card. Qed.

(** The round grew [I] by a factor [9/8], or [I] already exceeds [n/2].
    Decidable in Lean, a [bool] here. (Lean: [goodRound].) *)
Definition goodRound I r : bool :=
  (9 * #|I| <= 8 * #|step I r|)%N || (n < 2 * #|I|)%N.

(** Number of good rounds along a trajectory. (Lean: [goodCount].) *)
Fixpoint goodCount I s : nat :=
  if s is r :: s' then goodRound I r + goodCount (step I r) s' else 0.

(** An empty trajectory has no good rounds. (Lean: [goodCount_nil].) *)
Lemma goodCount_nil I : goodCount I [::] = 0%N.
Proof. by []. Qed.

(** The good rounds of a trajectory split off the head round.
    (Lean: [goodCount_cons].) *)
Lemma goodCount_cons I r s :
  goodCount I (r :: s) = (goodRound I r + goodCount (step I r) s)%N.
Proof. by []. Qed.

(** As long as the final informed set is still [<= n/2], each good round
    multiplied its size by [9/8]. (Lean: [pow_goodCount_mul_card_le_card_run].)
    *)
Lemma pow_goodCount_mul_card_le_card_run (R : realType) I s :
  (2 * #|run I s| <= n)%N ->
  (9 / 8 : R) ^+ goodCount I s * #|I|%:R <= #|run I s|%:R.
Proof.
elim: s I => [|r s IH] I; first by rewrite run_nil goodCount_nil expr0 mul1r.
rewrite run_cons goodCount_cons => h.
have hrun := subset_leq_card (subset_run (step I r) s).
have hstep := card_le_card_step I r.
have IHs := IH _ h.
have hpow : 0 <= (9 / 8 : R) ^+ goodCount (step I r) s by apply: exprn_ge0; lra.
have hnotbig : ~~ (n < 2 * #|I|)%N by rewrite -leqNgt; lia.
have hstepR : #|I|%:R <= #|step I r|%:R :> R by rewrite ler_nat.
rewrite /goodRound (negbTE hnotbig) orbF.
have [h98|h98] := boolP (9 * #|I| <= 8 * #|step I r|)%N; last first.
  by rewrite add0n; nra.
have : 9 * #|I|%:R <= 8 * #|step I r|%:R :> R by rewrite -!natrM ler_nat.
by rewrite add1n exprS; nra.
Qed.

End Model.
