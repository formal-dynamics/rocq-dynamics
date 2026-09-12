(** * Dynamics.prelude — shared imports, options and smoke checks

    Every other file of the development starts with
    [From Dynamics Require Import prelude.].

    Design (mirrors the Lean development formal-dynamics/leanamycs):
    - Reals are mathcomp-analysis's [R : realType]; [expR] and [ln] come from
      [mathcomp.analysis.exp]. Nothing else from analysis is used: no measure
      theory, no Lebesgue integral, no [probability T R].
    - Probability is FINITE and UNIFORM throughout: the expectation of
      [f : T -> R] on a [finType] [T] is [(\sum_(a : T) f a) / #|T|%:R].
    - Classical logic is mathcomp-classical's [boolp]; the only axioms any
      theorem may depend on are the three [boolp] axioms (see verify.sh). *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets reals sequences exp.
From mathcomp Require Import ring lra zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.

(** ** Smoke checks

    These exercise each dependency once so that a broken toolchain fails at
    [make] time with a clear message rather than deep inside a proof. *)

Lemma prelude_classical (P : Prop) : P \/ ~ P.
Proof. by case: (pselect P); [left | right]. Qed.

Lemma prelude_reals (R : realType) : (0 : R) < 1.
Proof. exact: ltr01. Qed.

Lemma prelude_expR (R : realType) : expR (0 : R) = 1.
Proof. exact: expR0. Qed.

Lemma prelude_ln (R : realType) : ln (1 : R) = 0.
Proof. exact: ln1. Qed.

Lemma prelude_bigop (R : realType) (n : nat) :
  \sum_(i < n) (1 : R) = n%:R.
Proof. by rewrite sumr_const card_ord. Qed.

Lemma prelude_lra (R : realType) (x : R) : 0 <= x -> x <= 1 -> x * x <= x.
Proof. by move=> x0 x1; nra. Qed.

Lemma prelude_lia (n m : nat) : (n <= m)%N -> (n.*2 <= m + m)%N.
Proof. by move=> ?; lia. Qed.

(** The headline of the smoke layer, audited by [verify.sh]. *)
Lemma prelude_smoke (R : realType) : expR (0 : R) + ln 1 = 1.
Proof. by rewrite expR0 ln1 addr0. Qed.
