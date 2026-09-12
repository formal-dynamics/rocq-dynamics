(** * Dynamics.rumor.growth — the growth phase

    Port of [RumorSpread/Growth.lean]. While the informed set has size at
    most [n/2], a round is good with probability at least [1/8]
    ([prob_goodRound]); the only concentration tool is the exponential-moment
    induction [expList_half_pow_goodCount]: [E[(1/2)^(good rounds)] <=
    (15/16)^T]. Phase 1 then follows by Markov. *)

From Dynamics Require Import prelude.
From Dynamics.prob Require Import avg bounds.
From Dynamics.rumor Require Import model oneround.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Growth.
Variable n : nat.
Context {R : realType}.
Implicit Types (I : {set 'I_n}).

(** Lean: [avg_half_pow_good]. The exponent is the boolean [goodRound I r]
    coerced to [nat] (Lean: [if goodRound I r then 1 else 0]). *)
Lemma avg_half_pow_good I :
  (2 <= n)%N -> I != finset.set0 ->
  avg (fun r : Tgt n => (1 / 2 : R) ^+ goodRound I r) <= 15 / 16.
Proof.
move=> hn hI.
have -> : (fun r : Tgt n => (1 / 2 : R) ^+ goodRound I r)
    = (fun r => 1 - 1 / 2 * (goodRound I r)%:R).
  by apply/funext => r; case: (goodRound I r); rewrite ?expr0 ?expr1 /=; lra.
rewrite avgB avgZ avg_const ?tgt_gt0 //.
by have := prob_goodRound (R := R) hn hI; lra.
Qed.

(** Lean: [expList_half_pow_goodCount] — exponential moment for adaptive
    Bernoulli trials. *)
Lemma expList_half_pow_goodCount k :
  (2 <= n)%N -> forall I, I != finset.set0 ->
  expList k (fun s : seq (Tgt n) => (1 / 2 : R) ^+ goodCount I s)
    <= (15 / 16) ^+ k.
Proof.
move=> hn; elim: k => [|k IH] I hI /=; first by rewrite expr0.
have key r : expList k (fun s => (1 / 2 : R) ^+ goodCount I (r :: s))
    = (1 / 2) ^+ goodRound I r
      * expList k (fun s => (1 / 2 : R) ^+ goodCount (step I r) s).
  by rewrite -expListZ; congr expList; apply/funext => s; rewrite /= exprD.
apply: le_trans (avg_le (g := fun r =>
    (15 / 16) ^+ k * (1 / 2) ^+ goodRound I r) _) _.
  move=> r; rewrite key mulrC; apply: ler_wpM2r; first by apply: exprn_ge0; lra.
  apply: IH; rewrite -card_gt0; apply: leq_trans (card_le_card_step I r).
  by rewrite card_gt0.
rewrite avgZ exprS.
have h1516 : 0 <= (15 / 16 : R) ^+ k by apply: exprn_ge0; lra.
by have := avg_half_pow_good hn hI; nra.
Qed.

(** Lean: [phase1] — starting from one informed node, after [k1] rounds the
    informed set is still [<= n/2] with probability at most
    [2^L (15/16)^k1], whenever [n <= (9/8)^L]. *)
Lemma phase1 (v0 : 'I_n) (L k1 : nat) :
  (2 <= n)%N -> n%:R <= (9 / 8 : R) ^+ L ->
  expList k1 (fun s : seq (Tgt n) => ((2 * #|run [set v0] s| <= n)%N)%:R : R)
    <= 2 ^+ L * (15 / 16) ^+ k1.
Proof.
move=> hn hL.
have hpt s : ((2 * #|run [set v0] s| <= n)%N)%:R
    <= 2 ^+ L * (1 / 2 : R) ^+ goodCount [set v0] s.
  have h12 : 0 <= (1 / 2 : R) ^+ goodCount [set v0] s by apply: exprn_ge0; lra.
  case: leqP => /= [h|_]; last by apply: mulr_ge0 => //; apply: exprn_ge0.
  have hgrow := pow_goodCount_mul_card_le_card_run R h.
  rewrite cards1 mulr1 in hgrow.
  have h1 : (1 <= #|run [set v0] s|)%N.
    by rewrite -(cards1 v0); apply: subset_leq_card; apply: subset_run.
  have hgL : (9 / 8 : R) ^+ goodCount [set v0] s < (9 / 8) ^+ L.
    apply: le_lt_trans hgrow _; apply: lt_le_trans _ hL.
    by rewrite ltr_nat; apply: leq_trans h; rewrite ltn_Pmull.
  rewrite ltr_eXn2l in hgL; last by lra.
  have h2 : (2 : R) ^+ goodCount [set v0] s <= 2 ^+ L.
    by apply: ler_weXn2l; [lra | exact: ltnW].
  rewrite -[leLHS](expr1n _ (goodCount [set v0] s)).
  rewrite -[1 in leLHS](_ : 2 * (1 / 2) = 1 :> R); last by lra.
  by rewrite exprMn; apply: ler_wpM2r.
apply: le_trans (expList_le k1 hpt) _; rewrite expListZ.
apply: ler_wpM2l; first by apply: exprn_ge0.
by apply: expList_half_pow_goodCount; rewrite // -card_gt0 cards1.
Qed.

End Growth.
