Require Import SLC.Lib.
Require Import SLC.Booleans.
Require Import SLC.PropBool.

Ltac t := (* program_simpl || *)
  libStep ||
  ifthenelse_step ||
  t_bool ||
  t_propbool ||
  destruct_refinement ||
  (autounfold with refinements in *).

Obligation Tactic := repeat t.
