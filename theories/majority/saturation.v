(** * Dynamics.majority.saturation — the saturation phase

    Port of [ThreeMajority/Saturation.lean]. Three stages take the dissent
    count [U = n - |I|] from at most [n/4] to exactly [0]: a geometric
    descent by [7/10] per round over [T2a n = ⌈6 ln n⌉] rounds down to the
    floor [500 ln n] (stage 2a), one round from that floor to the constant
    [10] (stage 2b), and one Markov step to [0] (stage 2c). The per-round
    bounds are the mean-scaled Chernoff bounds of [Dynamics.prob.chernoff]
    applied to the dissent decomposition [Y_dis]. *)

From Dynamics Require Import prelude.
From Dynamics.prob Require Import avg indep bounds chernoff.
From Dynamics.majority Require Import model oneround.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Saturation.
Variable n : nat.
Context {R : realType}.
Implicit Types (I : {set 'I_n}).

(** Lean's [⌈x⌉₊] for [x >= 0] (duplicate of [Dynamics.rumor.main.ceiln];
    both move to the prelude at its next rebuild). *)
Definition ceiln (x : R) : nat := `|Num.ceil x|.

(** Lean: [saturation_round_closed] — closed-form per-round upper tail. *)
Lemma saturation_round_closed I (M k : R) :
  (1 <= n)%N -> 0 < M -> M <= n%:R / 4 -> 5 / 8 * M <= k ->
  n%:R - #|I|%:R <= M ->
  avg (fun r : Tgt3 n => ((k <= n%:R - #|step I r|%:R :> R))%:R : R)
    <= expR (k - 5 / 8 * M - k * ln (k / (5 / 8 * M))).
Proof. Admitted.

(** Lean: [saturation_round_generic] — per-round upper tail from an upper
    bound on the mean dissent. *)
Lemma saturation_round_generic I (mub k : R) :
  (1 <= n)%N -> 0 < mub -> mub <= k -> \sum_(v < n) avg (Y_dis I v) <= mub ->
  avg (fun r : Tgt3 n => ((k <= n%:R - #|step I r|%:R :> R))%:R : R)
    <= expR (k - mub - k * ln (k / mub)).
Proof. Admitted.

(** Lean: [saturation_mean_quad] — the mean dissent is at most [3 M^2 / n]. *)
Lemma saturation_mean_quad I (M : R) :
  (1 <= n)%N -> 0 <= M -> n%:R - #|I|%:R <= M ->
  \sum_(v < n) avg (Y_dis I v) <= 3 * M ^+ 2 / n%:R.
Proof. Admitted.

(** Lean: [saturation_round_numeric]. *)
Lemma saturation_round_numeric I (M k : R) :
  (1 <= n)%N -> 0 < M -> M <= n%:R / 4 -> 5 / 8 * M <= k -> 0 < k ->
  n%:R - #|I|%:R <= M ->
  avg (fun r : Tgt3 n => ((k <= n%:R - #|step I r|%:R :> R))%:R : R)
    <= expR (- (k - 5 / 8 * M) ^+ 2 / (k + 5 / 8 * M)).
Proof. Admitted.

(** Lean: [saturation_round_contract] — dissent contracts by [7/10] except
    with probability [exp(-M / 250)]. *)
Lemma saturation_round_contract I (M : R) :
  (1 <= n)%N -> 0 < M -> M <= n%:R / 4 -> n%:R - #|I|%:R <= M ->
  avg (fun r : Tgt3 n => ((7 / 10 * M <= n%:R - #|step I r|%:R :> R))%:R : R)
    <= expR (- (1 / 250) * M).
Proof. Admitted.

(** Lean: [satAfter n M i = max (500 ln n) ((7/10)^i M)] — the deterministic
    dissent target after [i] rounds. *)
Definition satAfter (M : R) (i : nat) : R :=
  Num.max (500 * ln n%:R) ((7 / 10) ^+ i * M).

(** Lean: [satAfter_ge_floor]. *)
Lemma satAfter_ge_floor M i : 500 * ln n%:R <= satAfter M i.
Proof. Admitted.

(** Lean: [satAfter_zero]. *)
Lemma satAfter0 M : 500 * ln n%:R <= M -> satAfter M 0 = M.
Proof. Admitted.

(** Lean: [satAfter_le_of_le]. *)
Lemma satAfter_le M i :
  0 <= M -> M <= n%:R / 4 -> 500 * ln n%:R <= n%:R / 4 :> R ->
  satAfter M i <= n%:R / 4.
Proof. Admitted.

(** Lean: [satAfter_contract_le]. *)
Lemma satAfter_contract_le M i :
  (1 <= n)%N -> 7 / 10 * satAfter M i <= satAfter M i.+1.
Proof. Admitted.

(** Lean: [saturation_fail_le] — stage 2a, union bound. *)
Lemma saturation_fail_le (M : R) j :
  (2 <= n)%N -> 500 * ln n%:R <= M -> M <= n%:R / 4 ->
  500 * ln n%:R <= n%:R / 4 :> R ->
  forall i I, n%:R - #|I|%:R <= satAfter M i ->
  expList j (fun s : seq (Tgt3 n) =>
     ((satAfter M (i + j) < n%:R - #|run I s|%:R :> R))%:R : R)
    <= j%:R * expR (- 2 * ln n%:R).
Proof. Admitted.

(** Lean: [T2a n = ⌈6 log n⌉₊]. *)
Definition T2a : nat := ceiln (6 * ln n%:R).

(** Lean: [satAfter_quarter_le_floor]. *)
Lemma satAfter_quarter_le_floor :
  (2 <= n)%N -> satAfter (n%:R / 4) T2a <= 500 * ln n%:R.
Proof. Admitted.

(** Lean: [saturation_stage2a]. *)
Lemma saturation_stage2a (I0 : {set 'I_n}) :
  (2 <= n)%N -> 500 * ln n%:R <= n%:R / 4 :> R ->
  n%:R - #|I0|%:R <= n%:R / 4 :> R ->
  expList T2a (fun s : seq (Tgt3 n) =>
     ((500 * ln n%:R < n%:R - #|run I0 s|%:R :> R))%:R : R)
    <= T2a%:R * expR (- 2 * ln n%:R).
Proof. Admitted.

(** Lean: [saturation_stage2b]. *)
Lemma saturation_stage2b I :
  30 <= ln n%:R :> R -> n%:R - #|I|%:R <= 500 * ln n%:R :> R ->
  avg (fun r : Tgt3 n => ((10 <= n%:R - #|step I r|%:R :> R))%:R : R)
    <= expR (- ln n%:R).
Proof. Admitted.

(** Lean: [saturation_stage2c]. *)
Lemma saturation_stage2c I :
  (1 <= n)%N -> n%:R - #|I|%:R <= 10 :> R ->
  avg (fun r : Tgt3 n => ((1 <= n%:R - #|step I r|%:R :> R))%:R : R)
    <= 300 / n%:R.
Proof. Admitted.

End Saturation.

(* [T2a] has type [nat] but depends on [R] through [ln]; make [R] explicit so
   that [T2a n R] is well-formed outside the section. *)
Arguments T2a : clear implicits.
