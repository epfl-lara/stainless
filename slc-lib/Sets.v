Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import SLC.Tactics.
Require Import SLC.PropBool.

Open Scope bool_scope.

Definition set A := A -> bool.

Definition set_intersection {A} (s1 s2 : set A) x := s1 x && s2 x.

Definition set_union {A} (s1 s2 : set A) x := s1 x || s2 x.

Definition set_mem {A} (s: set A) x := s x.
Definition set_elem_of {A} x (s: set A) := set_mem s x. (* alias *)

Definition set_subset {A} (s1 s2 : set A): bool :=
  propInBool (forall x, implb (s1 x) (s2 x) = true).

Definition set_equality {A} (s1 s2 : set A): bool :=
  propInBool (s1 = s2).

Definition set_difference {A} (s1 s2: set A) x := s1 x && negb (s2 x).

Notation "s1 '==' s2" := (set_equality s1 s2) (at level 50).


Hint Unfold set_intersection : sets.

Definition set_empty {A}: set A := fun (x: A) => false.
Definition set_singleton {A} (x: A): set A := fun (y: A) => propInBool (x = y).

Hint Unfold set_elem_of : sets.
Hint Unfold set_union : sets.
Hint Unfold set_mem : sets.
Hint Unfold set_subset : sets.
Hint Unfold set_equality : sets.
Hint Unfold set_empty : sets.
Hint Unfold set_singleton : sets.
Hint Unfold set_difference : sets.

Ltac t_sets_aux :=
  autounfold with sets in *;
    repeat t_base || firstorder.

Lemma union_empty_l:
  forall {T} (s: set T), set_union s set_empty = s.
Proof.
  intros; apply functional_extensionality; t_sets_aux.
  autorewrite with libBool in *; intuition.
Qed.

Lemma union_empty_r:
  forall {T} (s: set T), set_union set_empty s = s.
Proof.
  intros; apply functional_extensionality; t_sets_aux.
Qed.

Hint Resolve union_empty_l union_empty_r: sets.

Ltac t_sets := t_sets_aux; try firstorder; eauto with sets.
