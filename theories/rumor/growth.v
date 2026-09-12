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
Proof. Admitted.

(** Lean: [expList_half_pow_goodCount] — exponential moment for adaptive
    Bernoulli trials. *)
Lemma expList_half_pow_goodCount k :
  (2 <= n)%N -> forall I, I != finset.set0 ->
  expList k (fun s : seq (Tgt n) => (1 / 2 : R) ^+ goodCount I s)
    <= (15 / 16) ^+ k.
Proof. Admitted.

(** Lean: [phase1] — starting from one informed node, after [k1] rounds the
    informed set is still [<= n/2] with probability at most
    [2^L (15/16)^k1], whenever [n <= (9/8)^L]. *)
Lemma phase1 (v0 : 'I_n) (L k1 : nat) :
  (2 <= n)%N -> n%:R <= (9 / 8 : R) ^+ L ->
  expList k1 (fun s : seq (Tgt n) => ((2 * #|run [set v0] s| <= n)%N)%:R : R)
    <= 2 ^+ L * (15 / 16) ^+ k1.
Proof. Admitted.

End Growth.
