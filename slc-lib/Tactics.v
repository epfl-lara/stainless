Require Import SLC.Lib.
Require Import SLC.Booleans.
Require Import SLC.PropBool.
Require Import SLC.Unfolding.

Ltac t_base := (* program_simpl || *)
  libStep ||
  t_bool ||
  t_propbool ||
  rewrite_equations ||
  rewrite_unfoldings ||
  rewrite_let ||
  autorewrite with libBoolExists in * |- ||
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

Notation "'<' x '>'" := (exist _ x _).
Notation "'‵' a" := (proj1_sig a) (at level 50).