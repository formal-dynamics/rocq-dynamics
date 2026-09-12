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

(** Lean: [Tgt3 n := Fin n → Fin n × Fin n × Fin n]. The triple is
    right-nested exactly as in Lean, so [s.1], [s.2.1], [s.2.2] match. *)
Notation Tgt3 n := {ffun 'I_n -> 'I_n * ('I_n * 'I_n)}.

(** Lean: [tgt3_nonempty]. *)
Lemma tgt3_gt0 (n : nat) : (1 <= n)%N -> (0 < #|Tgt3 n|)%N.
Proof.
by case: n => // n _; apply/card_gt0P; exists [ffun _ => (ord0, (ord0, ord0))].
Qed.

Section Model.
Variable n : nat.
Implicit Types (I : {set 'I_n}) (r : Tgt3 n) (s : seq (Tgt3 n)) (v : 'I_n)
  (t : 'I_n * ('I_n * 'I_n)).

(** Lean: [sampleCountOf] — how many of the three samples lie in [I]. *)
Definition sampleCountOf I t : nat :=
  (t.1 \in I) + (t.2.1 \in I) + (t.2.2 \in I).

(** Lean: [sampleCount]. *)
Definition sampleCount I r v : nat := sampleCountOf I (r v).

(** Lean: [step] — agents at least two of whose samples lie in [I]. *)
Definition step I r : {set 'I_n} := [set v | (2 <= sampleCount I r v)%N].

(** Lean: [mem_step]. *)
Lemma mem_step I r v : (v \in step I r) = (2 <= sampleCount I r v)%N.
Proof. by rewrite inE. Qed.

(** Lean: [sampleCount_mono]. *)
Lemma sampleCount_mono I I' r v :
  I \subset I' -> (sampleCount I r v <= sampleCount I' r v)%N.
Proof.
move/fintype.subsetP=> sub.
have h x : ((x \in I) <= (x \in I'))%N.
  by case xI: (x \in I); rewrite ?(sub _ xI).
exact: leq_add (leq_add (h _) (h _)) (h _).
Qed.

(** Lean: [step_mono] — the monotone coupling. *)
Lemma step_mono I I' r : I \subset I' -> step I r \subset step I' r.
Proof.
move=> sub; apply/fintype.subsetP=> v; rewrite !inE => /leq_trans; apply.
exact: sampleCount_mono.
Qed.

(** Lean: [card_step_le]. *)
Lemma card_step_le I r : (#|step I r| <= n)%N.
Proof. by rewrite -[X in (_ <= X)%N](card_ord n) max_card. Qed.

(** Lean: [run]. *)
Fixpoint run I s : {set 'I_n} :=
  if s is r :: s' then run (step I r) s' else I.

(** Lean: [run_nil]. *)
Lemma run_nil I : run I [::] = I.
Proof. by []. Qed.

(** Lean: [run_cons]. *)
Lemma run_cons I r s : run I (r :: s) = run (step I r) s.
Proof. by []. Qed.

(** Lean: [run_append]. *)
Lemma run_cat I s1 s2 : run I (s1 ++ s2) = run (run I s1) s2.
Proof. by elim: s1 I => [|r s IH] I //=; exact: IH. Qed.

(** Lean: [run_mono] — monotone coupling along a whole trajectory. *)
Lemma run_mono I I' s : I \subset I' -> run I s \subset run I' s.
Proof.
by elim: s I I' => [|r s IH] I I' //= sub; apply: IH; apply: step_mono.
Qed.

End Model.
