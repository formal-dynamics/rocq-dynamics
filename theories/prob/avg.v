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

(** Expectation of [f] under the uniform distribution on [T]: the sum of its
    values, divided by [#|T|].
    (Lean: [avg f = (∑ a, f a) / (Fintype.card α : ℝ)].) *)
Definition avg {T} (f : T -> R) : R := (\sum_(a : T) f a) / #|T|%:R.

(** A pointwise nonnegative function has nonnegative average.
    (Lean: [avg_nonneg].) *)
Lemma avg_ge0 T (f : T -> R) : (forall a, 0 <= f a) -> 0 <= avg f.
Proof.
by move=> f0; rewrite /avg divr_ge0 ?ler0n //; apply: sumr_ge0.
Qed.

(** [avg] is monotone: a pointwise inequality between functions passes to
    their averages. Together with [avg_ind] this is the only form of Markov's
    inequality the development needs. (Lean: [avg_le_avg].) *)
Lemma avg_le T (f g : T -> R) : (forall a, f a <= g a) -> avg f <= avg g.
Proof.
move=> fg; rewrite /avg; apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
exact: ler_sum.
Qed.

(** [avg] is additive. (Lean: [avg_add].) *)
Lemma avgD T (f g : T -> R) : avg (fun a => f a + g a) = avg f + avg g.
Proof. by rewrite /avg big_split mulrDl. Qed.

(** [avg] commutes with pointwise subtraction. (Lean: [avg_sub].) *)
Lemma avgB T (f g : T -> R) : avg (fun a => f a - g a) = avg f - avg g.
Proof. by rewrite /avg sumrB mulrBl. Qed.

(** [avg] is homogeneous: a constant factor comes out of the average.
    (Lean: [avg_const_mul].) *)
Lemma avgZ T (c : R) (f : T -> R) : avg (fun a => c * f a) = c * avg f.
Proof. by rewrite /avg -mulr_sumr mulrA. Qed.

(** The average of a finite sum is the sum of the averages.
    (Lean: [avg_sum].) *)
Lemma avg_sum T (I : Type) (r : seq I) (P : pred I) (f : I -> T -> R) :
  avg (fun a => \sum_(i <- r | P i) f i a) = \sum_(i <- r | P i) avg (f i).
Proof. by rewrite /avg exchange_big /= mulr_suml. Qed.

(** The expectation of an indicator is a counting ratio: the proportion of
    [T] that satisfies [P]. The indicator of a boolean is written [b%:R].
    (Lean: [avg_indicator].) *)
Lemma avg_ind T (P : pred T) :
  avg (fun a => (P a)%:R : R) = #|[pred a | P a]|%:R / #|T|%:R.
Proof.
rewrite /avg; congr (_ / _); rewrite -sum1_card natr_sum [in RHS]big_mkcond /=.
by apply: eq_bigr => a _; rewrite inE; case: (P a).
Qed.

(** A nonempty finite type has positive cardinality in [R] — the form needed
    to divide by [#|T|]. (Lean: [card_cast_pos], where [Nonempty α] becomes
    [0 < #|T|].) *)
Lemma card_gt0R T : (0 < #|T|)%N -> (0 : R) < #|T|%:R.
Proof. by rewrite ltr0n. Qed.

(** The average of a constant over a nonempty type is that constant.
    (Lean: [avg_const].) *)
Lemma avg_const T (c : R) : (0 < #|T|)%N -> avg (fun _ : T => c) = c.
Proof.
by move=> T0; rewrite /avg sumr_const -[in X in X / _]mulr_natr mulfK // pnatr_eq0 -lt0n.
Qed.

(** ** Expectation over [k] i.i.d. uniform draws

    [expList k F] averages the trajectory functional [F] over [k] independent
    uniform draws, in transition-operator form: the head draw is averaged out
    first. (Lean: [expList α T F].) *)
Fixpoint expList {T} (k : nat) (F : seq T -> R) : R :=
  match k with
  | 0 => F [::]
  | k'.+1 => avg (fun a : T => expList k' (fun s => F (a :: s)))
  end.

(** Empty horizon: no draw is made and [F] is evaluated at the empty
    trajectory. (Lean: [expList_zero].) *)
Lemma expList0 T (F : seq T -> R) : expList 0 F = F [::].
Proof. by []. Qed.

(** Conditioning on the first round: averaging over the head draw leaves an
    expectation over the remaining [k] rounds. The equation holds by
    definition, which is what makes conditioning free here.
    (Lean: [expList_succ].) *)
Lemma expListS T k (F : seq T -> R) :
  expList k.+1 F = avg (fun a : T => expList k (fun s => F (a :: s))).
Proof. by []. Qed.

(** [expList] is nonnegative on nonnegative functionals.
    (Lean: [expList_nonneg].) *)
Lemma expList_ge0 T k (F : seq T -> R) :
  (forall s, 0 <= F s) -> 0 <= expList k F.
Proof.
elim: k F => [|k IH] F F0 /=; first exact: F0.
by apply: avg_ge0 => a; apply: IH.
Qed.

(** [expList] is monotone: a pointwise bound on trajectories passes to the
    expectation. (Lean: [expList_le_expList].) *)
Lemma expList_le T k (F G : seq T -> R) :
  (forall s, F s <= G s) -> expList k F <= expList k G.
Proof.
elim: k F G => [|k IH] F G FG /=; first exact: FG.
by apply: avg_le => a; apply: IH.
Qed.

(** [expList] is additive. (Lean: [expList_add].) *)
Lemma expListD T k (F G : seq T -> R) :
  expList k (fun s => F s + G s) = expList k F + expList k G.
Proof.
elim: k F G => [|k IH] F G //=.
by rewrite -avgD; congr avg; apply/funext => a /=; rewrite IH.
Qed.

(** [expList] is homogeneous. (Lean: [expList_const_mul].) *)
Lemma expListZ T k (c : R) (F : seq T -> R) :
  expList k (fun s => c * F s) = c * expList k F.
Proof.
elim: k F => [|k IH] F //=.
by rewrite -avgZ; congr avg; apply/funext => a /=; rewrite IH.
Qed.

(** Constants pass through [expList] unchanged on a nonempty type.
    (Lean: [expList_const].) *)
Lemma expList_const T k (c : R) :
  (0 < #|T|)%N -> expList k (fun _ : seq T => c) = c.
Proof.
move=> T0; elim: k => [|k IH] //=.
by rewrite -[in RHS](avg_const c T0); congr avg; apply/funext => a.
Qed.

(** The expectation over [k1 + k2] rounds is the iterated expectation over
    [k1] then [k2] rounds — the conditioning idiom used to glue the growth and
    saturation phases. (Lean: [expList_append].) *)
Lemma expList_cat T k1 k2 (F : seq T -> R) :
  expList (k1 + k2) F
    = expList k1 (fun s1 => expList k2 (fun s2 => F (s1 ++ s2))).
Proof.
elim: k1 F => [|k1 IH] F //=.
by congr avg; apply/funext => a /=; rewrite IH.
Qed.

End Avg.

Arguments avg {R T} f.
Arguments expList {R T} k F.
