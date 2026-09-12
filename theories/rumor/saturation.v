(** * Dynamics.rumor.saturation — the saturation phase

    Port of [RumorSpread/Saturation.lean]. Once the informed set exceeds
    [n/2], the expected number of uninformed nodes contracts by a factor
    [2/3] per round ([avg_uninformed_le]); iterating through [expList] gives
    the geometric decay, and Markov finishes the argument in
    [Dynamics.rumor.main]. *)

From Dynamics Require Import prelude.
From Dynamics.prob Require Import avg.
From Dynamics.rumor Require Import model oneround.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Saturation.
Variable n : nat.
Context {R : realType}.

(** Lean: [saturation]. *)
Lemma saturation k :
  (2 <= n)%N -> forall I : {set 'I_n}, (n <= 2 * #|I|)%N ->
  expList k (fun s : seq (Tgt n) => n%:R - #|run I s|%:R : R)
    <= (2 / 3) ^+ k * (n%:R - #|I|%:R).
Proof. Admitted.

End Saturation.
