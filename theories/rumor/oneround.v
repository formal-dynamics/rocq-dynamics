(** * Dynamics.rumor.oneround — one-round estimates for the push protocol

    Port of [RumorSpread/OneRound.lean]. The only *computed* probability of
    the development is [avg_not_contacted]: a fixed uninformed node is missed
    by every push with probability exactly [(1 - 1/(n-1)) ^ |I|], obtained by
    counting the round configurations that avoid it. Everything else here is
    an expectation bound derived from it with the Bernoulli-type inequalities
    of [Dynamics.prob.bounds]. *)

From Dynamics Require Import prelude.
From Dynamics.prob Require Import avg bounds.
From Dynamics.rumor Require Import model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** [foldr muln 1] over a mapped list is a [\prod_] bigop; this is the shape
    in which [card_dep_ffun]/[card_family] deliver dependent-function
    cardinalities. *)
Lemma foldr_muln_map (T : Type) (g : T -> nat) (s : seq T) :
  foldr muln 1 [seq g v | v <- s] = (\prod_(v <- s) g v)%N.
Proof. by elim: s => [|v s ih]; rewrite ?big_nil //= big_cons ih. Qed.

(** Each of the [n] nodes independently picks one of the [n - 1] others, so a
    round is a uniform draw from a space of size [(n - 1) ^ n].
    (Lean: [card_tgt].) *)
Lemma card_tgt (n : nat) : #|Tgt n| = ((n - 1) ^ n)%N.
Proof.
rewrite card_dep_ffun /image_mem foldr_muln_map big_enum /=.
rewrite (eq_bigr (fun _ => (n - 1)%N)) => [|v _].
  by rewrite prod_nat_const card_ord.
by rewrite card_sig cardC1 card_ord subn1.
Qed.

Section OneRound.
Variable n : nat.
Implicit Types (I : {set 'I_n}) (r : Tgt n) (u v : 'I_n).

(** The nodes distinct from two given ones — the counting input to the
    one-round estimates. (Lean: [card_subtype_ne_ne].) *)
Lemma card_sig_ne_ne v u :
  v != u -> #|{: {x : 'I_n | (x != v) && (x != u)}}| = (n - 2)%N.
Proof.
move=> vu; rewrite card_sig.
have := cardC [pred x : 'I_n | (x != v) && (x != u)]; rewrite card_ord.
have -> : #|[predC [pred x : 'I_n | (x != v) && (x != u)]]| = 2%N.
  rewrite (eq_card (B := pred2 v u)) ?card2 ?vu // => x.
  by rewrite !inE negb_and !negbK.
by move=> h; rewrite -[in RHS]h addnK.
Qed.

(** The configurations in which no member of [I] targets [u]. (Lean:
    [card_filter_not_contacted].) *)
Lemma card_not_contacted I u :
  u \notin I ->
  #|[set r : Tgt n | [forall v in I, val (r v) != u]]|
    = ((n - 2) ^ #|I| * (n - 1) ^ (n - #|I|))%N.
Proof.
move=> uI.
pose F : forall v : 'I_n, pred {x : 'I_n | x != v} :=
  fun v => if v \in I then [pred x : {x : 'I_n | x != v} | val x != u]
           else predT.
rewrite (eq_card (B := (family F : simpl_pred (Tgt n)))) => [|r]; last first.
  rewrite inE; apply/forall_inP/familyP => h v.
    by rewrite /F; case: ifP => // vI; rewrite inE; apply: h.
  by move=> vI; have := h v; rewrite /F vI.
rewrite card_family /image_mem foldr_muln_map big_enum /=.
rewrite (bigID (mem I)) /=.
rewrite [X in (X * _)%N](eq_bigr (fun _ => (n - 2)%N)) => [|v vI]; last first.
  have vu : u != v by apply: contraNneq uI => ->.
  rewrite /F vI; have := cardC [pred x : {x : 'I_n | x != v} | val x != u].
  rewrite card_sig cardC1 card_ord.
  have -> : #|[predC [pred x : {x : 'I_n | x != v} | val x != u]]| = 1%N.
    rewrite (eq_card (B := pred1 (exist (fun x => x != v) u vu))) ?card1 //.
    by move=> x; rewrite !inE negbK -val_eqE.
  by move=> h; rewrite (_ : (n - 2 = n.-1 - 1)%N); [rewrite -h addnK | lia].
rewrite [X in (_ * X)%N](eq_bigr (fun _ => (n - 1)%N)) => [|v vI]; last first.
  by rewrite /F (negbTE vI) card_sig cardC1 card_ord subn1.
rewrite prod_nat_const (eq_bigl (fun v => v \in ~: I)) => [|v]; last first.
  by rewrite finset.in_setC.
rewrite prod_nat_const; congr (_ ^ _ * _ ^ _)%N.
by have := cardsC I; rewrite card_ord => h; rewrite -[X in (X - _)%N]h addKn.
Qed.

Context {R : realType}.

(** The contact probability. (Lean: [avg_not_contacted].) *)
Lemma avg_not_contacted I u :
  (2 <= n)%N -> u \notin I ->
  avg (fun r : Tgt n => (u \notin step I r)%:R : R)
    = (1 - 1 / (n%:R - 1)) ^+ #|I|.
Proof.
move=> n2 uI.
have -> : (fun r : Tgt n => (u \notin step I r)%:R : R)
    = fun r => ([forall v in I, val (r v) != u])%:R.
  apply/funext => r.
  suff -> : (u \notin step I r) = [forall v in I, val (r v) != u] by [].
  apply/idP/idP.
    move=> uS; apply/forall_inP => v vI; apply: contraNneq uS => vu.
    by apply/mem_step; right; exists v.
  move=> /forall_inP h; apply/negP => /mem_step[uI'|[v vI vu]].
    by rewrite uI' in uI.
  by have := h v vI; rewrite vu eqxx.
rewrite (avg_ind (fun r : Tgt n => [forall v in I, val (r v) != u])).
have := card_not_contacted uI.
rewrite (eq_card (B := [pred r : Tgt n | [forall v in I, val (r v) != u]]))
  => [-> | r]; last by rewrite !inE.
rewrite card_tgt natrM !natrX !natrB //; last by lia.
have hI : (#|I| <= n)%N by rewrite -[leqRHS](card_ord n) max_card.
have n1 : n%:R - 1 != 0 :> R.
  have h2 : 2 <= n%:R :> R by rewrite ler_nat.
  by rewrite subr_eq0 gt_eqF //; lra.
rewrite -[in X in _ / _ ^+ X](subnKC hI) exprD invfM mulrACA.
rewrite divff ?mulr1; last exact: expf_neq0.
rewrite -expr_div_n; congr (_ ^+ _).
have := divff n1; lra.
Qed.

(** Expected size after one round. (Lean: [avg_card_step].) *)
Lemma avg_card_step I :
  (2 <= n)%N ->
  avg (fun r : Tgt n => #|step I r|%:R : R)
    = #|I|%:R + (n%:R - #|I|%:R) * (1 - (1 - 1 / (n%:R - 1)) ^+ #|I|).
Proof.
move=> n2; have T0 := tgt_gt0 n2.
have -> : (fun r : Tgt n => #|step I r|%:R : R)
    = fun r => #|I|%:R + \sum_(u | u \notin I) (u \in step I r)%:R.
  apply/funext => r; rewrite -sum1_card natr_sum big_mkcond /=.
  rewrite (bigID (mem I)) /=; congr (_ + _).
    rewrite -[in RHS]sum1_card natr_sum; apply: eq_bigr => u uI.
    by rewrite (fintype.subsetP (subset_step I r)).
  by apply: eq_bigr => u _; case: (u \in step I r).
rewrite avgD avg_const // avg_sum; congr (_ + _).
rewrite (eq_bigr (fun _ => 1 - (1 - 1 / (n%:R - 1)) ^+ #|I|)) => [|u uI].
  rewrite (eq_bigl (fun v => v \in ~: I)) => [|v]; last first.
    by rewrite finset.in_setC.
  rewrite sumr_const -[LHS]mulr_natl; congr (_ * _).
  have := cardsC I; rewrite card_ord => h.
  by rewrite -[X in X%:R - _]h natrD addrAC subrr add0r.
have -> : (fun r : Tgt n => (u \in step I r)%:R : R)
    = fun r => 1 - (u \notin step I r)%:R.
  apply/funext => r; case: (u \in step I r).
    by rewrite /= mulr1n mulr0n subr0.
  by rewrite /= mulr1n mulr0n subrr.
by rewrite avgB avg_const // avg_not_contacted.
Qed.

(** A good round has probability at least [1/8]. (Lean: [prob_goodRound].) *)
Lemma prob_goodRound I :
  (2 <= n)%N -> I != finset.set0 ->
  1 / 8 <= avg (fun r : Tgt n => (goodRound I r)%:R : R).
Proof.
move=> n2 I0; have T0 := tgt_gt0 n2.
have m1 : 1 <= #|I|%:R :> R by rewrite -card_gt0 in I0; rewrite ler1n.
have [big|big] := boolP (n < 2 * #|I|)%N.
  have -> : (fun r : Tgt n => (goodRound I r)%:R : R) = fun _ => 1.
    by apply/funext => r; rewrite /goodRound big orbT.
  by rewrite avg_const //; lra.
(* pointwise reverse Markov: |step I r| <= 9m/8 + m 1[good] *)
have hpt r :
    #|step I r|%:R <= 9 * #|I|%:R / 8 + #|I|%:R * (goodRound I r)%:R :> R.
  have h2 : #|step I r|%:R <= 2 * #|I|%:R :> R.
    by rewrite -natrM ler_nat card_step_le.
  rewrite /goodRound (negbTE big) orbF.
  have [h9|h9] := boolP (9 * #|I| <= 8 * #|step I r|)%N.
    by rewrite mulr1n; lra.
  rewrite mulr0n; rewrite -ltnNge in h9.
  have : 8 * #|step I r|%:R < 9 * #|I|%:R :> R by rewrite -!natrM ltr_nat.
  lra.
have havg := avg_le hpt.
rewrite avgD avg_const // avgZ in havg.
(* expected growth: m + m/4 <= E|step| *)
have hgrow :
    #|I|%:R + #|I|%:R / 4 <= avg (fun r : Tgt n => #|step I r|%:R) :> R.
  rewrite avg_card_step //.
  rewrite -leqNgt in big.
  have hmn : 2 * #|I|%:R <= n%:R :> R by rewrite -natrM ler_nat.
  have hn2 : 2 <= n%:R :> R by rewrite ler_nat.
  have n1 : 0 < n%:R - 1 :> R by lra.
  have hx0 : 0 <= 1 / (n%:R - 1) :> R by rewrite divr_ge0 //; lra.
  have hxmul : 1 / (n%:R - 1) * (n%:R - 1) = 1 :> R.
    by rewrite div1r mulVf // gt_eqF.
  have hx1 : 1 / (n%:R - 1) <= 1 :> R by nra.
  have hmx : #|I|%:R * (1 / (n%:R - 1)) <= 1 :> R by nra.
  have hkey := half_mul_le_one_sub_pow hx0 hx1 hmx.
  have hnm : 0 <= n%:R - #|I|%:R :> R by lra.
  have h1 := ler_wpM2l hnm hkey.
  have hnmx : 1 / 2 <= (n%:R - #|I|%:R) * (1 / (n%:R - 1)) :> R by nra.
  have h2 : #|I|%:R / 4
      <= (n%:R - #|I|%:R) * (#|I|%:R * (1 / (n%:R - 1)) / 2) :> R by nra.
  lra.
nra.
Qed.

(** Above half, the expected uninformed count contracts by [2/3]. (Lean:
    [avg_uninformed_le].) *)
Lemma avg_uninformed_le I :
  (2 <= n)%N -> (n <= 2 * #|I|)%N ->
  avg (fun r : Tgt n => n%:R - #|step I r|%:R : R)
    <= 2 / 3 * (n%:R - #|I|%:R).
Proof.
move=> n2 half; have T0 := tgt_gt0 n2.
rewrite avgB avg_const // avg_card_step //.
have hn2 : 2 <= n%:R :> R by rewrite ler_nat.
have hmn : n%:R <= 2 * #|I|%:R :> R by rewrite -natrM ler_nat.
have hcard : #|I|%:R <= n%:R :> R.
  by rewrite ler_nat -[leqRHS](card_ord n) max_card.
have n1 : 0 < n%:R - 1 :> R by lra.
have hx0 : 0 <= 1 / (n%:R - 1) :> R by rewrite divr_ge0 //; lra.
have hxmul : 1 / (n%:R - 1) * (n%:R - 1) = 1 :> R.
  by rewrite div1r mulVf // gt_eqF.
have hx1 : 1 / (n%:R - 1) <= 1 :> R by nra.
have hb := pow_one_sub_le_one_div #|I| hx0 hx1.
have hmx : 1 / 2 <= #|I|%:R * (1 / (n%:R - 1)) :> R by nra.
have hb23 : (1 - 1 / (n%:R - 1)) ^+ #|I| <= 2 / 3 :> R.
  by apply: le_trans hb _; rewrite ler_pdivrMr; lra.
have hnm : 0 <= n%:R - #|I|%:R :> R by lra.
have := ler_wpM2l hnm hb23.
lra.
Qed.

End OneRound.
