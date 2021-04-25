Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import SLC.PropBool.
Require Import SLC.Booleans.
Require Import SLC.Lib.

Open Scope bool_scope.

Definition set A := A -> bool.

Definition set_intersection {A} (s1 s2 : set A) x := s1 x && s2 x.

Definition set_union {A} (s1 s2 : set A) x := s1 x || s2 x.

Definition set_elem_of {A} x (s: set A) := s x.

Definition set_subset {A} (s1 s2 : set A): bool :=
  propInBool (forall x, s1 x = true -> s2 x = true).
Notation "s1 '⊆' s2" := (set_subset s1 s2) (at level 50).

Definition set_equality {A} (s1 s2 : set A): bool :=
  (s1 ⊆ s2) && (s2 ⊆ s1).

Definition set_difference {A} (s1 s2: set A) x := s1 x && negb (s2 x).

Definition set_empty {A}: set A := fun (x: A) => false.
Definition set_singleton {A} (x: A): set A := fun (y: A) => propInBool (x = y).

Notation "s1 '==' s2" := (set_equality s1 s2) (at level 50).
Notation "s1 '∪' s2" := (set_union s1 s2) (at level 10).
Notation "s1 '∩' s2" := (set_intersection s1 s2) (at level 10).
Notation "s1 '∖' s2" := (set_difference s1 s2) (at level 10).
Notation "x '∈' s" := (set_elem_of x s) (at level 20).
Notation "'{{' s '}}'" := (set_singleton s) (at level 50).
Notation "'∅'" := (set_empty) (at level 50).

Hint Unfold set_elem_of : i_sets.
Hint Unfold set_union : i_sets.
Hint Unfold set_intersection : i_sets.
Hint Unfold set_subset : i_sets.
Hint Unfold set_equality : i_sets.
Hint Unfold set_empty : i_sets.
Hint Unfold set_singleton : i_sets.
Hint Unfold set_difference : i_sets.

Hint Unfold set_equality: core.

Ltac t_sets_aux :=
  autounfold with i_sets in *;
    repeat fast || firstorder.

Lemma union_empty_l:
  forall T (s: set T), set_union s set_empty = s.
Proof.
  intros; apply functional_extensionality; repeat t_sets_aux || rewrite orb_false_r.
Qed.

Lemma union_empty_r:
  forall T (s: set T), set_union set_empty s = s.
Proof.
  intros; apply functional_extensionality; t_sets_aux.
Qed.

Hint Rewrite union_empty_l union_empty_r: libSet.

Lemma in_union:
  forall T (s1 s2: set T) x,
    (x ∈ s1 ∪ s2) =
    (
      (x ∈ s1) ||
      (x ∈ s2)
    ).
Proof.
  repeat fast || t_sets_aux || autorewrite with libBool in *.
Qed.

Lemma in_intersection:
  forall T (s1 s2: set T) x,
    (x ∈ s1 ∩ s2) =
    (
      (x ∈ s1) &&
      (x ∈ s2)
    ).
Proof.
  repeat fast || t_sets_aux || autorewrite with libBool in *.
Qed.

Lemma in_singleton:
  forall T (x y: T),
    (x ∈ {{ y }}) = (propInBool (x = y)).
Proof.
  repeat fast || t_sets_aux || autorewrite with libProp in *.
Qed.

Lemma in_emptyset:
  forall T (x: T),
    (x ∈ ∅) = false.
Proof.
  repeat fast || t_sets_aux || autorewrite with libProp in *.
Qed.

Lemma in_difference:
  forall T x (s1 s2: set T),
    x ∈ s1 ∖ s2 = x ∈ s1 && negb (x ∈ s2).
Proof.
  repeat fast || t_sets_aux || autorewrite with libProp in *.
Qed.


Hint Rewrite in_union: libSet.
Hint Rewrite in_intersection: libSet.
Hint Rewrite in_singleton: libSet.
Hint Rewrite in_difference: libSet.
Hint Rewrite in_emptyset: libSet.


Lemma subset_union:
  forall T (s s1 s2: set T),
    (s1 ∪ s2 ⊆ s) =
    (
      (s1 ⊆ s) &&
      (s2 ⊆ s)
    ).
Proof.
  repeat fast ||
         autounfold with i_sets in * ||
         autorewrite with libProp in *; eauto.
  apply equal_booleans; repeat fast || autorewrite with libProp libBool in * || apply_any.
Qed.

Hint Rewrite subset_union: libSet.

Lemma subset_union_true:
  forall T (s s1 s2: set T),
    (s1 ⊆ s = true) ->
    (s2 ⊆ s = true) ->
    (s1 ∪ s2 ⊆ s = true).
Proof.
  repeat fast ||
         autounfold with i_sets in * ||
         autorewrite with libProp libBool in *.
Qed.

Hint Resolve subset_union_true: b_sets.


Lemma subset_intersection:
  forall T (s s1 s2: set T),
    (s ⊆ s1 ∩ s2) =
    (
      (s ⊆ s1) &&
      (s ⊆ s2)
    ).
Proof.
  repeat fast ||
         autounfold with i_sets in * ||
         autorewrite with libProp in *; eauto.
  apply equal_booleans; repeat fast || autorewrite with libProp libBool in * || apply_any;
    firstorder (repeat fast || autorewrite with libBool in *).
Qed.

Hint Rewrite subset_intersection: libSet.

Lemma subset_intersection_true:
  forall T (s s1 s2: set T),
    (s ⊆ s1 = true) ->
    (s ⊆ s2 = true) ->
    (s ⊆ s1 ∩ s2 = true).
Proof.
  repeat fast ||
         autounfold with i_sets in * ||
         autorewrite with libProp libBool in *.
Qed.

Hint Resolve subset_intersection_true: b_sets.


Lemma subset_difference:
  forall T (s s1 s2: set T),
    (s ⊆ s1 ∖ s2) =
    (
      (s ⊆ s1) &&
      (s ∩ s2 == ∅)
    ).
Proof.
  repeat fast ||
         autounfold with i_sets in * ||
         autorewrite with libProp in *; eauto.
  apply equal_booleans;
    repeat fast || autorewrite with libProp libBool in * || instantiate_any.
  - destruct (s2 x) eqn:S; repeat t_bool || fast.
    unshelve epose proof (H2 x _); repeat fast || autorewrite with libBool in *.
Qed.

Hint Rewrite subset_difference: libSet.

Lemma subset_difference_true:
  forall T (s s1 s2: set T),
    (s ⊆ s1 = true) ->
    ((s ∩ s2 == ∅) = true) ->
    (s ⊆ s1 ∖ s2 = true).
Proof.
  repeat fast ||
         autounfold with i_sets in * ||
         autorewrite with libProp libBool in *.
  destruct (s2 x) eqn:S; repeat t_bool || fast.
  unshelve epose proof (H2 x _); repeat fast || autorewrite with libBool in *.
Qed.

Hint Resolve subset_difference_true: b_sets.


Lemma singleton_subset:
  forall T (x: T) s,
    ({{ x }} ⊆ s) = (x ∈ s).
Proof.
  repeat fast || autounfold with i_sets in *.
  apply equal_booleans; repeat fast || autorewrite with libProp in * || apply_any.
Qed.

Hint Rewrite singleton_subset: libSet.

Lemma empty_subset:
  forall T (s: set T),
    (∅ ⊆ s) = true.
Proof.
  repeat fast || autounfold with i_sets in * || autorewrite with libProp in *.
Qed.

Hint Rewrite empty_subset: libSet.

Lemma subset_union1:
  forall T (s s1 s2: set T),
    (s ⊆ s1) = true ->
    (s ⊆ (s1 ∪ s2)) = true.
Proof.
  repeat fast || autounfold with i_sets in * || autorewrite with libProp libBool in *.
Qed.

Lemma subset_union2:
  forall T (s s1 s2: set T),
    (s ⊆ s2) = true ->
    (s ⊆ (s1 ∪ s2)) = true.
Proof.
  repeat fast || autounfold with i_sets in * || autorewrite with libProp libBool in *.
Qed.

Lemma subset_middle:
  forall T (s s1 s2 s3: set T),
    (s ⊆ s2) = true ->
    (s ⊆ (s1 ∪ s2) ∪ s3) = true.
Proof.
  repeat fast || autounfold with i_sets in * || autorewrite with libProp libBool in *.
Qed.

Lemma subset_middle2:
  forall T (s s1 s2 s3: set T),
    (s ⊆ s2) = true ->
    (s ⊆ s1 ∪ (s2 ∪ s3)) = true.
Proof.
  repeat fast || autounfold with i_sets in * || autorewrite with libProp libBool in *.
Qed.

Hint Immediate subset_union1 subset_union2: b_sets.
Hint Immediate subset_middle subset_middle2: b_sets.

Lemma factor_left:
  forall T (a b c d: set T),
    (a ∪ b) ∩ c ⊆ d = (a ∩ c ⊆ d) && (b ∩ c ⊆ d).
Proof.
  repeat fast || autounfold with i_sets in * || autorewrite with libProp libBool in *.
  apply equal_booleans;
    repeat fast || autounfold with i_sets in * || autorewrite with libProp libBool in *;
    firstorder (repeat fast || autorewrite with libBool in *).
Qed.


Lemma factor_left2:
  forall T (a b c d: set T),
    c ∩ (a ∪ b) ⊆ d = (c ∩ a ⊆ d) && (c ∩ b ⊆ d).
Proof.
  repeat fast || autounfold with i_sets in * || autorewrite with libProp libBool in *.
  apply equal_booleans;
    repeat fast || autounfold with i_sets in * || autorewrite with libProp libBool in *;
    firstorder (repeat fast || autorewrite with libBool in *).
Qed.

Hint Rewrite factor_left factor_left2: libSet.


Lemma singleton_intersect_subset:
  forall T x (s1 s2: set T),
    ({{ x }} ∩ s1 ⊆ s2) = ((negb (x ∈ s1)) || x ∈ s2).
Proof.
  repeat fast || autounfold with i_sets in * || autorewrite with libProp libBool in *.
  apply equal_booleans;
    repeat fast || autorewrite with libProp libBool in *.
  - destruct (s1 x) eqn:E; repeat fast.
    right. apply_any; repeat fast || autorewrite with libProp libBool in *.
Qed.

Hint Rewrite singleton_intersect_subset: libSet.

Lemma subset_refl:
  forall T (s: set T),
    s ⊆ s = true.
Proof.
  repeat fast || autounfold with i_sets in * || autorewrite with libProp in *.
Qed.

Hint Rewrite subset_refl: libSet.

Lemma subset_trans:
  forall T (s1 s2 s3: set T),
    (s1 ⊆ s2 = true) ->
    (s2 ⊆ s3 = true) ->
    (s1 ⊆ s3 = true).
Proof.
  repeat fast || autounfold with i_sets in * || autorewrite with libProp in *.
Qed.

Lemma subset_union3:
  forall T (s1 s2: set T),
    s1 ⊆ (s1 ∪ s2) = true.
Proof.
  repeat fast || autounfold with i_sets in * || autorewrite with libProp libBool in *.
Qed.

Lemma subset_union4:
  forall T (s1 s2: set T),
    s2 ⊆ (s1 ∪ s2) = true.
Proof.
  repeat fast || autounfold with i_sets in * || autorewrite with libProp libBool in *.
Qed.

Lemma subset_intersection3:
  forall T (s1 s2: set T),
    (s1 ∩ s2) ⊆ s1 = true.
Proof.
  repeat fast || autounfold with i_sets in * || autorewrite with libProp libBool in *.
Qed.

Lemma subset_intersection4:
  forall T (s1 s2: set T),
    (s1 ∩ s2) ⊆ s2 = true.
Proof.
  repeat fast || autounfold with i_sets in * || autorewrite with libProp libBool in *.
Qed.

Hint Rewrite subset_union3: libSet.
Hint Rewrite subset_union4: libSet.
Hint Rewrite subset_intersection3: libSet.
Hint Rewrite subset_intersection4: libSet.

Lemma diff_union:
  forall T (s1 s2 s3: set T),
    (s1 ∪ s2) ∖ s3 = (s1 ∖ s3) ∪ (s2 ∖ s3).
Proof.
  repeat fast || autounfold with i_sets in * || autorewrite with libProp libBool in *.
  apply functional_extensionality; repeat fast.
  destruct (s1 x) eqn:E1; repeat fast;
  destruct (s2 x) eqn:E2; repeat fast;
  destruct (s3 x) eqn:E3; repeat fast.
Qed.

Hint Rewrite diff_union: libSet.

Lemma diff_singleton:
  forall T (a: T),
    ({{ a }} ∖ {{ a }}) = ∅.
Proof.
  repeat fast || autounfold with i_sets in * || apply functional_extensionality.
  destruct (B@(a = x)); repeat fast.
Qed.

Lemma diff_singleton2:
  forall T (a b: T),
    ({{ a }} ∖ {{ b }}) = if (B@(a = b)) then ∅ else {{ a }}.
Proof.
  repeat fast || ifthenelse_step || autounfold with i_sets in * || apply functional_extensionality ||
         autorewrite with libProp in * ||
         match goal with
         | |- context[propInBool ?P] =>
           let H := fresh "H" in
           destruct (propInBool P) eqn:H
         end.
Qed.

Lemma diff_singleton3:
  forall T (a: T) (s: set T),
    ({{ a }} ∖ s) = if (a ∈ s) then ∅ else {{ a }}.
Proof.
  repeat fast || ifthenelse_step || autounfold with i_sets in * || apply functional_extensionality ||
         autorewrite with libProp in * || t_bool ||
         match goal with
         | |- context[propInBool ?P] =>
           let H := fresh "H" in
           destruct (propInBool P) eqn:H
         | H: context[propInBool ?P] |- _ =>
           let H := fresh "H" in
           destruct (propInBool P) eqn:H
         end.
Qed.

Hint Rewrite diff_singleton3: libSet.
Hint Rewrite diff_singleton2: libSet.
Hint Rewrite diff_singleton: libSet.


Hint Resolve subset_union3: b_sets.
Hint Resolve subset_union4: b_sets.
Hint Resolve subset_intersection3: b_sets.
Hint Resolve subset_intersection4: b_sets.

Ltac t_sets :=
  match goal with
  | H: ?s1 ⊆ ?s2 = true |- ?s1 ⊆ ?s3 = true =>
    apply subset_trans with s2;
    solve [ repeat fast || autorewrite with libSet libBool libProp in *; auto 3 with b_sets ]
  | H: ?s2 ⊆ ?s3 = true |- ?s1 ⊆ ?s3 = true =>
    apply subset_trans with s2;
    solve [ repeat fast || autorewrite with libSet libBool libProp in *; auto 3 with b_sets ]
  end.
