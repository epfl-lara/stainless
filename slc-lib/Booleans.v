Require Import SLC.Lib.

Require Import Coq.Bool.Bool.
Require Import ZArith.

Hint Rewrite eqb_true_iff: libR.
Hint Rewrite eqb_false_iff: libR.
Hint Rewrite <- Zeq_is_eq_bool: libR.
Hint Rewrite orb_true_iff: libR.

Definition bool_and b1 (b2: true = b1 -> bool): bool :=
  match b1 as B return (B = b1 -> bool) with
  | true => b2
  | false => fun _ => false
  end eq_refl.

Notation "b1 &b b2" := (bool_and b1 (fun _ => b2)) (at level 80, right associativity).

Lemma bool_and_iff: forall b1 b2,
    (b1 &b b2) = true <-> b1 = true /\ b2 = true.
  unfold bool_and; repeat libStep.
Qed.

Hint Rewrite bool_and_iff: libR.

Notation "b1 &&b b2" := (if b1 then b2 else false) (at level 50). 

Lemma rewrite_and_true:
  forall b: bool, b &&b true = b.
Proof.
  repeat libStep.
Qed.

Lemma rewrite_true_and:
  forall b: bool, true &&b b = b.
Proof.
  repeat libStep.
Qed.

Lemma rewrite_and_false:
  forall b: bool, b &&b false = false.
Proof.
  repeat libStep.
Qed.

Lemma rewrite_false_and:
  forall b: bool, false &&b b = false.
Proof.
  repeat libStep.
Qed.

Hint Rewrite rewrite_and_true: libR.
Hint Rewrite rewrite_true_and: libR.
Hint Rewrite rewrite_and_false: libR.
Hint Rewrite rewrite_false_and: libR.

Ltac literal b :=
  (unify b true) + (unify b false).

Ltac not_literal b := tryif literal b then fail else idtac.

Ltac t_bool :=
  match goal with
  | |- ?b1 = ?b2 => not_literal b1; not_literal b2; apply eq_iff_eq_true
  end.
