(** * Dynamics.prob.indep — independence over a product space

    Port of the second half of [ThreeMajority/Prob.lean]: the discrete,
    measure-theory-free statement that the average of a *product* of
    functions of *different* coordinates over a product of finite types
    equals the product of the individual averages. This is the independence
    fact that lets the 3-majority protocol's per-agent updates (one round,
    [n] agents, each sampling independently) be combined into a single
    concentration bound for the whole round ([Dynamics.prob.chernoff]). *)

From Dynamics Require Import prelude.
From Dynamics.prob Require Import avg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.


Section Indep.
Context {R : realType}.

(** Lean: [avg_mul_prod] — independence for a pair of coordinates. No
    nonemptiness hypothesis: if either factor is empty both sides are [0]. *)
Lemma avg_mul_prod (B D : finType) (g : B -> R) (h : D -> R) :
  avg (fun p : B * D => g p.1 * h p.2) = avg g * avg h.
Proof.
by rewrite /avg card_prod natrM invfM mulrACA big_distrlr pair_bigA.
Qed.

(** Lean: [avg_fst_mul] — marginal on the first coordinate. *)
Lemma avg_fst (B D : finType) (g : B -> R) :
  (0 < #|D|)%N -> avg (fun p : B * D => g p.1) = avg g.
Proof.
move=> D0; rewrite -[RHS](mulr1 (avg g)) -(avg_const (1 : R) D0) -avg_mul_prod.
by congr avg; apply/funext => p /=; rewrite mulr1.
Qed.

(** Lean: [avg_snd_mul] — marginal on the second coordinate. *)
Lemma avg_snd (B D : finType) (h : D -> R) :
  (0 < #|B|)%N -> avg (fun p : B * D => h p.2) = avg h.
Proof.
move=> B0; rewrite -[RHS](mul1r (avg h)) -(avg_const (1 : R) B0) -avg_mul_prod.
by congr avg; apply/funext => p /=; rewrite mul1r.
Qed.

(** Lean: [avg_equiv] — reindexing [avg] along a bijection. *)
Lemma avg_bij (T U : finType) (e : T -> U) (F : U -> R) :
  bijective e -> avg (fun a => F (e a)) = avg F.
Proof.
move=> bije; rewrite /avg (bij_eq_card bije); congr (_ / _).
by rewrite [RHS](reindex e) //; exact: onW_bij.
Qed.

(** Lean: [avg_prod_pi] — independence over an ['I_n]-indexed product: the
    average of [\prod_i f i (x i)] over the product type [{ffun 'I_n -> G}]
    equals the product of the averages [avg (f i)]. *)
Lemma avg_prod_ffun (G : finType) (n : nat) (f : 'I_n -> G -> R) :
  avg (fun x : {ffun 'I_n -> G} => \prod_(i < n) f i (x i))
    = \prod_(i < n) avg (f i).
Proof.
rewrite /avg -bigA_distr_bigA card_ffun card_ord natrX.
by rewrite [RHS]big_split /= prodr_const card_ord exprVn.
Qed.

(** Lean: [avg_eval] — marginal of a single coordinate of the product. *)
Lemma avg_eval (G : finType) (n : nat) (v : 'I_n) (F : G -> R) :
  (0 < #|G|)%N -> avg (fun x : {ffun 'I_n -> G} => F (x v)) = avg F.
Proof.
move=> G0; pose f (i : 'I_n) (g : G) : R := if i == v then F g else 1.
have key (H : G -> R) (x : {ffun 'I_n -> G}) :
    \prod_(i < n) (if i == v then H (x i) else 1) = H (x v).
  by rewrite (bigD1 v) //= eqxx big1 ?mulr1 // => i /negbTE ->.
transitivity (avg (fun x : {ffun 'I_n -> G} => \prod_(i < n) f i (x i))).
  by congr avg; apply/funext => x; rewrite /f key.
rewrite avg_prod_ffun (bigD1 v) //= {1}/f eqxx big1 ?mulr1 // => i iv.
by rewrite /f (negbTE iv) avg_const.
Qed.

End Indep.
