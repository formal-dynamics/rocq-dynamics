(** * Dynamics.majority.model — the 3-majority process on the complete graph

    Port of [ThreeMajority/Model.lean] (Lean namespace [ThreeMajority]).

    - [Tgt3 n] — a round configuration: every agent draws an ordered triple
      of samples, independently and uniformly, *with* replacement.
    - [step I r] — one round: every agent adopts the majority opinion among
      its three samples' current membership in the opinion-[1] set [I].
    - [run I s] — the opinion-[1] set after consuming the list [s] of rounds.
    - [step_mono] — the monotone coupling: for a fixed round [r], [step] is
      monotone in [I] (though not in the round index). This single
      combinatorial fact replaces the martingale machinery a non-monotone
      process would otherwise need. *)

From Dynamics Require Import prelude.
From Dynamics.prob Require Import avg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** A round configuration: every agent draws an ordered triple of samples,
    independently and uniformly, *with* replacement. The triple is
    right-nested exactly as in Lean, so [s.1], [s.2.1], [s.2.2] match.
    (Lean: [Tgt3 n := Fin n → Fin n × Fin n × Fin n].) *)
Notation Tgt3 n := {ffun 'I_n -> 'I_n * ('I_n * 'I_n)}.

(** There is at least one round configuration as soon as [n >= 1], so
    averaging over [Tgt3 n] is meaningful. (Lean: [tgt3_nonempty].) *)
Lemma tgt3_gt0 (n : nat) : (1 <= n)%N -> (0 < #|Tgt3 n|)%N.
Proof.
by case: n => // n _; apply/card_gt0P; exists [ffun _ => (ord0, (ord0, ord0))].
Qed.

Section Model.
Variable n : nat.
Implicit Types (I : {set 'I_n}) (r : Tgt3 n) (s : seq (Tgt3 n)) (v : 'I_n)
  (t : 'I_n * ('I_n * 'I_n)).

(** How many of the three samples lie in [I]. (Lean: [sampleCountOf].) *)
Definition sampleCountOf I t : nat :=
  (t.1 \in I) + (t.2.1 \in I) + (t.2.2 \in I).

(** How many of agent [v]'s three samples lie in [I], under round [r].
    (Lean: [sampleCount].) *)
Definition sampleCount I r v : nat := sampleCountOf I (r v).

(** Agents at least two of whose samples lie in [I]. (Lean: [step].) *)
Definition step I r : {set 'I_n} := [set v | (2 <= sampleCount I r v)%N].

(** An agent holds opinion [1] after the round exactly when at least two of
    its samples did. (Lean: [mem_step].) *)
Lemma mem_step I r v : (v \in step I r) = (2 <= sampleCount I r v)%N.
Proof. by rewrite inE. Qed.

(** Growing the opinion-[1] set can only increase an agent's sample count —
    the pointwise core of the monotone coupling.
    (Lean: [sampleCount_mono].) *)
Lemma sampleCount_mono I I' r v :
  I \subset I' -> (sampleCount I r v <= sampleCount I' r v)%N.
Proof.
move/fintype.subsetP=> sub.
have h x : ((x \in I) <= (x \in I'))%N.
  by case xI: (x \in I); rewrite ?(sub _ xI).
exact: leq_add (leq_add (h _) (h _)) (h _).
Qed.

(** The monotone coupling. (Lean: [step_mono].) *)
Lemma step_mono I I' r : I \subset I' -> step I r \subset step I' r.
Proof.
move=> sub; apply/fintype.subsetP=> v; rewrite !inE => /leq_trans; apply.
exact: sampleCount_mono.
Qed.

(** A round leaves at most all [n] agents holding opinion [1].
    (Lean: [card_step_le].) *)
Lemma card_step_le I r : (#|step I r| <= n)%N.
Proof. by rewrite -[X in (_ <= X)%N](card_ord n) max_card. Qed.

(** The opinion-[1] set after consuming the list [s] of rounds: fold [step]
    over [s]. (Lean: [run].) *)
Fixpoint run I s : {set 'I_n} :=
  if s is r :: s' then run (step I r) s' else I.

(** No rounds, no change. (Lean: [run_nil].) *)
Lemma run_nil I : run I [::] = I.
Proof. by []. Qed.

(** Peeling the first round off a trajectory. (Lean: [run_cons].) *)
Lemma run_cons I r s : run I (r :: s) = run (step I r) s.
Proof. by []. Qed.

(** Running a concatenation of round lists is running one list after the
    other — the trajectory counterpart of [expList_cat], used to split the
    growth and saturation phases. (Lean: [run_append].) *)
Lemma run_cat I s1 s2 : run I (s1 ++ s2) = run (run I s1) s2.
Proof. by elim: s1 I => [|r s IH] I //=; exact: IH. Qed.

(** Monotone coupling along a whole trajectory. (Lean: [run_mono].) *)
Lemma run_mono I I' s : I \subset I' -> run I s \subset run I' s.
Proof.
by elim: s I I' => [|r s IH] I I' //= sub; apply: IH; apply: step_mono.
Qed.

End Model.
