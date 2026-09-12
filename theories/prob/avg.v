(** * Dynamics.prob.avg — finite uniform probability

    Port of [RumorSpread/Prob.lean] and the shared part of
    [ThreeMajority/Prob.lean] (Lean namespaces [RumorPush], [ThreeMajority]).

    - [avg f] is the expectation of [f : T -> R] under the uniform distribution
      on the finite type [T]: a sum divided by a cardinality. When [T] is empty
      both sides are [0] (MathComp's [x / 0 = 0] convention), exactly as in
      Lean.
    - [expList k F] is the expectation of a trajectory functional
      [F : seq T -> R] over [k] i.i.d. uniform draws, defined by recursion on
      [k] so that conditioning on the first round is a definitional
      unfolding.

    Markov's inequality and union bounds are pointwise inequalities pushed
    through [avg_le] / [expList_le]; nothing else is needed. *)

From Dynamics Require Import prelude.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.


Section Avg.
Context {R : realType}.
Implicit Types (T : finType).

(** Lean: [avg f = (∑ a, f a) / (Fintype.card α : ℝ)]. *)
Definition avg {T} (f : T -> R) : R := (\sum_(a : T) f a) / #|T|%:R.

(** Lean: [avg_nonneg]. *)
Lemma avg_ge0 T (f : T -> R) : (forall a, 0 <= f a) -> 0 <= avg f.
Proof. Admitted.

(** Lean: [avg_le_avg] (this is Markov's inequality in disguise). *)
Lemma avg_le T (f g : T -> R) : (forall a, f a <= g a) -> avg f <= avg g.
Proof. Admitted.

(** Lean: [avg_add]. *)
Lemma avgD T (f g : T -> R) : avg (fun a => f a + g a) = avg f + avg g.
Proof. Admitted.

(** Lean: [avg_sub]. *)
Lemma avgB T (f g : T -> R) : avg (fun a => f a - g a) = avg f - avg g.
Proof. Admitted.

(** Lean: [avg_const_mul]. *)
Lemma avgZ T (c : R) (f : T -> R) : avg (fun a => c * f a) = c * avg f.
Proof. Admitted.

(** Lean: [avg_sum] — the average of a finite sum is the sum of the averages. *)
Lemma avg_sum T (I : Type) (r : seq I) (P : pred I) (f : I -> T -> R) :
  avg (fun a => \sum_(i <- r | P i) f i a) = \sum_(i <- r | P i) avg (f i).
Proof. Admitted.

(** Lean: [avg_indicator] — the expectation of an indicator is a counting
    ratio. The indicator of a boolean is written [b%:R]. *)
Lemma avg_ind T (P : pred T) :
  avg (fun a => (P a)%:R : R) = #|[pred a | P a]|%:R / #|T|%:R.
Proof. Admitted.

(** Lean: [card_cast_pos] ([Nonempty α] becomes [0 < #|T|]). *)
Lemma card_gt0R T : (0 < #|T|)%N -> (0 : R) < #|T|%:R.
Proof. Admitted.

(** Lean: [avg_const]. *)
Lemma avg_const T (c : R) : (0 < #|T|)%N -> avg (fun _ : T => c) = c.
Proof. Admitted.

(** ** Expectation over [k] i.i.d. uniform draws

    Lean: [expList α T F], transition-operator form (the head draw is
    averaged out first). *)
Fixpoint expList {T} (k : nat) (F : seq T -> R) : R :=
  match k with
  | 0 => F [::]
  | k'.+1 => avg (fun a : T => expList k' (fun s => F (a :: s)))
  end.

(** Lean: [expList_zero]. *)
Lemma expList0 T (F : seq T -> R) : expList 0 F = F [::].
Proof. Admitted.

(** Lean: [expList_succ]. *)
Lemma expListS T k (F : seq T -> R) :
  expList k.+1 F = avg (fun a : T => expList k (fun s => F (a :: s))).
Proof. Admitted.

(** Lean: [expList_nonneg]. *)
Lemma expList_ge0 T k (F : seq T -> R) :
  (forall s, 0 <= F s) -> 0 <= expList k F.
Proof. Admitted.

(** Lean: [expList_le_expList]. *)
Lemma expList_le T k (F G : seq T -> R) :
  (forall s, F s <= G s) -> expList k F <= expList k G.
Proof. Admitted.

(** Lean: [expList_add]. *)
Lemma expListD T k (F G : seq T -> R) :
  expList k (fun s => F s + G s) = expList k F + expList k G.
Proof. Admitted.

(** Lean: [expList_const_mul]. *)
Lemma expListZ T k (c : R) (F : seq T -> R) :
  expList k (fun s => c * F s) = c * expList k F.
Proof. Admitted.

(** Lean: [expList_const]. *)
Lemma expList_const T k (c : R) :
  (0 < #|T|)%N -> expList k (fun _ : seq T => c) = c.
Proof. Admitted.

(** Lean: [expList_append] — the expectation over [k1 + k2] rounds is the
    iterated expectation; this is the conditioning idiom used to glue the
    growth and saturation phases. *)
Lemma expList_cat T k1 k2 (F : seq T -> R) :
  expList (k1 + k2) F
    = expList k1 (fun s1 => expList k2 (fun s2 => F (s1 ++ s2))).
Proof. Admitted.

End Avg.

Arguments avg {R T} f.
Arguments expList {R T} k F.
