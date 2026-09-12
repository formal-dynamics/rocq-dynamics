(** * Dynamics.majority.main — 3-majority reaches consensus in [O(log n)] rounds

    Port of [ThreeMajority/Main.lean]. Glues the growth phase to the three
    saturation stages through the [expList] conditioning idiom and states
    the main theorem with the same constants as Lean: if [ln n >= 30] and
    the initial opinion-[1] set has at least [(3/5) n] agents, then after
    [10 + (⌈6 ln n⌉ + 2)] rounds all agents hold opinion [1] with
    probability at least [1 - 500/n]. *)

From Dynamics Require Import prelude.
From Dynamics.prob Require Import avg indep bounds chernoff.
From Dynamics.majority Require Import model oneround growth saturation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Main.
Variable n : nat.
Context {R : realType}.
Implicit Types (I : {set 'I_n}).

(** Lean: [ne_univ_iff_pos_dissent]. *)
Lemma neq_setT_dissent I :
  (I != [set: 'I_n]) = (1 <= n%:R - #|I|%:R :> R).
Proof. Admitted.

(** Lean: [hfloor4_of_hbig]. *)
Lemma floor4_of_big : 30 <= ln (n%:R : R) -> 500 * ln n%:R <= n%:R / 4 :> R.
Proof. Admitted.

(** Lean: [saturation_2b2c] — stages 2b and 2c combined. *)
Lemma saturation_2b2c I :
  30 <= ln (n%:R : R) -> n%:R - #|I|%:R <= 500 * ln n%:R :> R ->
  expList 2 (fun s : seq (Tgt3 n) => ((1 <= n%:R - #|run I s|%:R :> R))%:R : R)
    <= expR (- ln n%:R) + 300 / n%:R.
Proof. Admitted.

(** Lean: [saturation_2a2b2c] — all three saturation stages combined. *)
Lemma saturation_2a2b2c (I0 : {set 'I_n}) :
  30 <= ln (n%:R : R) -> n%:R - #|I0|%:R <= n%:R / 4 :> R ->
  expList (T2a n R + 2)
    (fun s : seq (Tgt3 n) => ((1 <= n%:R - #|run I0 s|%:R :> R))%:R : R)
    <= (T2a n R)%:R * expR (- 2 * ln n%:R) + (expR (- ln n%:R) + 300 / n%:R).
Proof. Admitted.

(** Lean: [majority3_consensus_fail_le] — main failure bound, raw form. *)
Theorem majority3_consensus_fail_le (I0 : {set 'I_n}) :
  30 <= ln (n%:R : R) -> n%:R * (3 / 5) <= #|I0|%:R :> R ->
  expList (10 + (T2a n R + 2))
    (fun s : seq (Tgt3 n) => ((1 <= n%:R - #|run I0 s|%:R :> R))%:R : R)
    <= 10 * expR (- (1 / 10 ^+ 7) * n%:R)
       + ((T2a n R)%:R * expR (- 2 * ln n%:R)
          + (expR (- ln n%:R) + 300 / n%:R)).
Proof. Admitted.

(** Lean: [majority3_consensus_fail_le_clean] — clean numeric bound. *)
Theorem majority3_consensus_fail_le_clean (I0 : {set 'I_n}) :
  30 <= ln (n%:R : R) -> n%:R * (3 / 5) <= #|I0|%:R :> R ->
  expList (10 + (T2a n R + 2))
    (fun s : seq (Tgt3 n) => ((1 <= n%:R - #|run I0 s|%:R :> R))%:R : R)
    <= 500 / n%:R.
Proof. Admitted.

(** Lean: [majority3_consensus_whp] — the main theorem. *)
Theorem majority3_consensus_whp (I0 : {set 'I_n}) :
  30 <= ln (n%:R : R) -> n%:R * (3 / 5) <= #|I0|%:R :> R ->
  1 - 500 / n%:R
    <= expList (10 + (T2a n R + 2))
         (fun s : seq (Tgt3 n) => (run I0 s == [set: 'I_n])%:R : R).
Proof. Admitted.

End Main.
