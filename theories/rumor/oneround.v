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

(** Lean: [card_tgt]. *)
Lemma card_tgt (n : nat) : #|Tgt n| = ((n - 1) ^ n)%N.
Proof. Admitted.

Section OneRound.
Variable n : nat.
Implicit Types (I : {set 'I_n}) (r : Tgt n) (u v : 'I_n).

(** Lean: [card_subtype_ne_ne]. *)
Lemma card_sig_ne_ne v u :
  v != u -> #|{: {x : 'I_n | (x != v) && (x != u)}}| = (n - 2)%N.
Proof. Admitted.

(** Lean: [card_filter_not_contacted] — the configurations in which no
    member of [I] targets [u]. *)
Lemma card_not_contacted I u :
  u \notin I ->
  #|[set r : Tgt n | [forall v in I, val (r v) != u]]|
    = ((n - 2) ^ #|I| * (n - 1) ^ (n - #|I|))%N.
Proof. Admitted.

Context {R : realType}.

(** Lean: [avg_not_contacted] — the contact probability. *)
Lemma avg_not_contacted I u :
  (2 <= n)%N -> u \notin I ->
  avg (fun r : Tgt n => (u \notin step I r)%:R : R)
    = (1 - 1 / (n%:R - 1)) ^+ #|I|.
Proof. Admitted.

(** Lean: [avg_card_step] — expected size after one round. *)
Lemma avg_card_step I :
  (2 <= n)%N ->
  avg (fun r : Tgt n => #|step I r|%:R : R)
    = #|I|%:R + (n%:R - #|I|%:R) * (1 - (1 - 1 / (n%:R - 1)) ^+ #|I|).
Proof. Admitted.

(** Lean: [prob_goodRound] — a good round has probability at least [1/8]. *)
Lemma prob_goodRound I :
  (2 <= n)%N -> I != finset.set0 ->
  1 / 8 <= avg (fun r : Tgt n => (goodRound I r)%:R : R).
Proof. Admitted.

(** Lean: [avg_uninformed_le] — above half, the expected uninformed count
    contracts by [2/3]. *)
Lemma avg_uninformed_le I :
  (2 <= n)%N -> (n <= 2 * #|I|)%N ->
  avg (fun r : Tgt n => n%:R - #|step I r|%:R : R)
    <= 2 / 3 * (n%:R - #|I|%:R).
Proof. Admitted.

End OneRound.
