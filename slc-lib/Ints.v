Require Import SLC.Lib.
Require Import ZArith.
Require Import stdpp.set.

Open Scope Z_scope.

Hint Rewrite Z.leb_gt: libR.
Hint Rewrite Z.leb_le: libR.
Hint Rewrite Z.geb_leb: libR.
Hint Rewrite <- Zgt_is_gt_bool: libR.
Hint Rewrite Z.geb_le: libR.

Lemma geb_le2: ∀ n m : Z, (m ≤ n)%Z -> (m <=? n)%Z = true.
Proof.
  repeat libStep.
Qed.
Lemma geb_le3: ∀ n m : Z, (m ≤ n)%Z -> (n >=? m)%Z = true.
Proof.
  repeat libStep.
Qed.
Lemma geb_le4: ∀ n m : Z, (m >= n)%Z -> (m >=? n)%Z = true.
Proof.
  repeat libStep || omega.
Qed.
Lemma geb_le5: ∀ n m : Z, (m >= n)%Z -> (n <=? n)%Z = true.
Proof.
  repeat libStep.
Qed.

Lemma Zeq_bool_neq2:
  ∀ x y : Z,  Zeq_bool x y = false <-> (x <> y).
Proof.
  intuition;
    repeat match goal with
           | _ => libStep
           | H: _ |- _ => apply Zeq_bool_neq in H
           | H: _ |- _ => apply Positive_as_OT.compare_eq in H
           | x: Z |- _ => destruct x
           | _ => progress (unfold Zeq_bool in *)
           | _ => progress (unfold CompOpp in *)
           end.
Qed.

Hint Rewrite Zeq_bool_neq2: libR.
