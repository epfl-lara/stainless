Require Import SLC.Lib.
Require Import SLC.Booleans.
Require Import SLC.PropBool.
Require Import SLC.Unfolding.
Require Import SLC.Sets.

Ltac t_base :=
  libStep ||
  t_bool ||
  t_propbool ||
  (autorewrite with libSet in *) ||
  t_sets ||
  rewrite_equations ||
  rewrite_unfoldings ||
  rewrite_let ||
  (autorewrite with libBoolExists in * |-) ||
  destruct_refinement ||
  (autounfold with refinements in *).

Notation "'<' x '>'" := (exist _ x _).
Notation "'‵' a" := (proj1_sig a) (at level 50).
