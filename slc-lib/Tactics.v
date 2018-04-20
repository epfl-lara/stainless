Require Import SLC.Lib.
Require Import SLC.Booleans.

Ltac t := (* program_simpl || *)
  libStep ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  t_bool ||
  destruct_refinement ||
  (autounfold with refinements in *).

Obligation Tactic := repeat t.
