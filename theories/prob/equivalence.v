(** * Dynamics.prob.equivalence — [expList] is the product-space average

    Port of [RumorSpread/Equivalence.lean]. [expList k F] was *defined* by
    recursion (average out the first draw, then recurse); this file proves it
    equals the textbook object: the uniform average of [F] over *all*
    length-[k] sequences of draws, i.e. over the product probability space of
    [k] i.i.d. uniform rounds.

    Lean states the product space as [Fin T → α] and reads a draw sequence
    off with [List.ofFn]; the MathComp counterpart is the finite type
    [k.-tuple T] of length-[k] sequences, read off with [tval] (the coercion
    to [seq T]). The bijection [Fin.consEquiv] of the Lean proof is
    [cons_tuple : T -> k.-tuple T -> k.+1.-tuple T]. *)

From Dynamics Require Import prelude.
From Dynamics.prob Require Import avg indep.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.


Section Equivalence.
Context {R : realType}.

(** Fubini for [avg] over a binary product (Lean: [Fintype.sum_prod_type]
    inline). Both sides are [0] when either factor is empty. *)
Lemma avg_pair (B D : finType) (G : B -> D -> R) :
  avg (fun p : B * D => G p.1 p.2) = avg (fun b => avg (fun d => G b d)).
Proof.
rewrite /avg card_prod natrM invfM -mulr_suml pair_bigA /=.
by rewrite mulrA mulrAC.
Qed.

(** Prepending a head to a tuple is a bijection [T * k.-tuple T ->
    k.+1.-tuple T] (Lean: [Fin.consEquiv]). *)
Lemma cons_tuple_bij (T : finType) k :
  bijective (fun p : T * k.-tuple T => cons_tuple p.1 p.2).
Proof.
exists (fun t : k.+1.-tuple T => (thead t, [tuple of behead t])).
  by case=> a t /=; rewrite theadE; congr (_, _); apply/val_inj.
by move=> t; apply/val_inj; case/tupleP: t => a t /=; rewrite theadE.
Qed.

(** Lean: [expList_eq_avg_ofFn] — the recursive expectation over [k] rounds
    is the uniform average over the product space [k.-tuple T] of all
    length-[k] draw sequences. *)
Lemma expList_eq_avg_tuple (T : finType) k (F : seq T -> R) :
  expList k F = avg (fun w : k.-tuple T => F w).
Proof.
elim: k F => [|k IH] F /=.
  have -> : (fun w : 0.-tuple T => F w) = fun _ => F [::].
    by apply/funext => w; rewrite [w]tuple0.
  by rewrite avg_const // card_tuple expn0.
have -> : (fun a : T => expList k (fun s => F (a :: s)))
    = fun a => avg (fun w : k.-tuple T => F (a :: w)).
  by apply/funext => a; rewrite IH.
rewrite -(avg_pair (fun a (w : k.-tuple T) => F (a :: w))).
by rewrite -[RHS](avg_bij _ (cons_tuple_bij T k)).
Qed.

End Equivalence.
