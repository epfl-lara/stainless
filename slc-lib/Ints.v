Require Import SLC.Lib.
Require Import SLC.Booleans.
Require Import ZArith.

Open Scope Z_scope.

Hint Rewrite Z.leb_gt: libInts.
Hint Rewrite Z.leb_le: libInts.
Hint Rewrite Z.geb_leb: libInts.
Hint Rewrite <- Zgt_is_gt_bool: libInts.
Hint Rewrite Z.geb_le: libInts.
Hint Rewrite Z.ltb_lt: libInts.
Hint Rewrite Z.ltb_ge: libInts.
Hint Rewrite <- Zeq_is_eq_bool: libInts.
(*
Lemma geb_le2: ∀ n m : Z, (m ≤ n)%Z -> (m <=? n)%Z = true.
Proof.
  intros; autorewrite with libInts in *; repeat fast.
Qed.
Lemma geb_le3: ∀ n m : Z, (m ≤ n)%Z -> (n >=? m)%Z = true.
Proof.
  intros; autorewrite with libInts in *; repeat fast.
Qed.
Lemma geb_le4: ∀ n m : Z, (m >= n)%Z -> (m >=? n)%Z = true.
Proof.
  intros; autorewrite with libInts in *; repeat fast; omega.
Qed.
Lemma geb_le5: ∀ n m : Z, (m >= n)%Z -> (n <=? n)%Z = true.
Proof.
  intros; autorewrite with libInts in *; repeat fast.
Qed.  

Lemma geb_le6: forall x y, ((x <= y) -> False) -> (x <=? y = false).
Proof.
  intros; autorewrite with libInts in *; repeat fast; omega.
Qed.

Lemma geb_rwrt: forall x y, (x < y) -> (y <= x) -> False.
Proof.
  intros; autorewrite with libInts in *; repeat fast; omega.
Qed.
*)


Lemma Zeq_bool_neq2:
  forall x y : Z,  Zeq_bool x y = false <-> (x <> y).
Proof.
  intuition;
    repeat match goal with
           | _ => libStep || ifthenelse_step
           | H: _ |- _ => apply Zeq_bool_neq in H
           | H: _ |- _ => apply Pos.compare_eq in H
           | x: Z |- _ => destruct x
           | _ => progress (unfold Zeq_bool in *)
           | _ => progress (unfold CompOpp in *)
           end.
Qed.
                           
Lemma Zeq_bool_neq3:
  forall x y : Z, false = Zeq_bool x y <-> (x <> y).
Proof.
  intuition.
  - apply eq_sym in H.
    rewrite Zeq_bool_neq2 in *; auto.
  - apply eq_sym.
    rewrite Zeq_bool_neq2 in *; auto.
Qed.

Hint Rewrite Zeq_bool_neq2: libInts.
Hint Rewrite Zeq_bool_neq3: libInts.
