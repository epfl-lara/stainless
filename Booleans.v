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

