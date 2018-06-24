Require Import SLC.Lib.

Definition test (x: nat): {y: nat | False }. Admitted.

Parameter x: nat.
Parameter z: nat.

Goal
  proj1_sig (test x) = z ->
  proj1_sig (test x) = z ->
  False.
Proof.
  intros.
  pose proof (Mark H "hello").
  destruct (test x) eqn:RR.
  Check RR. (* test x = test x *)
  