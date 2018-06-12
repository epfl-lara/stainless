Require Import SLC.Lib.
Require Import SLC.Booleans.
Require Import SLC.PropBool.

Ltac t_base := (* program_simpl || *)
  libStep ||
  t_bool ||
  t_propbool ||
  rewrite_equations ||
  destruct_refinement ||
  (autounfold with refinements in *).

(* Ltac t := 
  t_base ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t. *)
