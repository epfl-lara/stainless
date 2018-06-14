Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import SLC.Tactics.
Require Import SLC.PropBool.
Require Import SLC.Booleans.
Require Import SLC.Lib.

Open Scope bool_scope.

Definition set A := A -> bool.

Definition set_intersection {A} (s1 s2 : set A) x := s1 x && s2 x.

Definition set_union {A} (s1 s2 : set A) x := s1 x || s2 x.

Definition set_elem_of {A} x (s: set A) := s x.

Definition set_subset {A} (s1 s2 : set A): bool :=
  propInBool (forall x, implb (s1 x) (s2 x) = true).

Definition set_equality {A} (s1 s2 : set A): bool :=
  propInBool (s1 = s2).

Definition set_difference {A} (s1 s2: set A) x := s1 x && negb (s2 x).

Definition set_empty {A}: set A := fun (x: A) => false.
Definition set_singleton {A} (x: A): set A := fun (y: A) => propInBool (x = y).

Notation "s1 '==' s2" := (set_equality s1 s2) (at level 50).
Notation "s1 '⊆' s2" := (set_subset s1 s2) (at level 50).
Notation "s1 '∪' s2" := (set_union s1 s2) (at level 10).
Notation "s1 '∩' s2" := (set_intersection s1 s2) (at level 10).
Notation "x '∈' s" := (set_elem_of x s) (at level 20).
Notation "'{{' s '}}'" := (set_singleton s) (at level 50).
Notation "'∅'" := (set_empty) (at level 50).

Hint Unfold set_intersection : sets.

Hint Unfold set_elem_of : i_sets.
Hint Unfold set_union : i_sets.
Hint Unfold set_intersection : i_sets.
Hint Unfold set_subset : i_sets.
Hint Unfold set_equality : i_sets.
Hint Unfold set_empty : i_sets.
Hint Unfold set_singleton : i_sets.
Hint Unfold set_difference : i_sets.

Ltac t_sets_aux :=
  autounfold with i_sets in *;
    repeat t_base || firstorder.

Lemma union_empty_l:
  forall T (s: set T), set_union s set_empty = s.
Proof.
  intros; apply functional_extensionality; t_sets_aux.
  autorewrite with libBool in *; intuition.
Qed.

Lemma union_empty_r:
  forall T (s: set T), set_union set_empty s = s.
Proof.
  intros; apply functional_extensionality; t_sets_aux.
Qed.

Hint Rewrite union_empty_l union_empty_r: libSet.

Lemma in_union:
  forall T (s1 s2: set T) x,
    ((x ∈ s1 ∪ s2) = true) <->
    (
      ((x ∈ s1) = true) \/
      ((x ∈ s2) = true)
    ).
Proof.
  repeat fast || t_sets_aux || autorewrite with libBool in *.
Qed.  

Lemma in_intersection:
  forall T (s1 s2: set T) x,
    ((x ∈ s1 ∩ s2) = true) <->
    (
      ((x ∈ s1) = true) /\
      ((x ∈ s2) = true)
    ).
Proof.
  repeat fast || t_sets_aux || autorewrite with libBool in *.
Qed.  

Lemma in_singleton:
  forall T (x y: T),
    ((x ∈ {{ y }}) = true) <-> x = y.
Proof.
  repeat fast || t_sets_aux || autorewrite with libProp in *.
Qed.

Lemma in_emptyset:
  forall T (x: T),
    ((x ∈ ∅) = true) <-> False.
Proof.
  repeat fast || t_sets_aux || autorewrite with libProp in *.
Qed.
  
Hint Rewrite in_union: libSet.
Hint Rewrite in_intersection: libSet.
Hint Rewrite in_singleton: libSet.
Hint Rewrite in_emptyset: libSet.

Ltac t_sets := idtac.
