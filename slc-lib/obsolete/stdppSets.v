Require Import stdpp.set.
Require Import stdpp.base.

Require Import SLC.PropBool.
Require Import SLC.Lib.

Definition set_difference {A} (s1 s2: set A) := s1 ∖ s2.
Definition set_subset {A} (s1 s2 : set A): bool := propInBool (s1 ⊆ s2).
Definition set_equality {A} (s1 s2 : set A): bool := propInBool (s1 ≡ s2).
Definition set_intersection {A} (s1 s2: set A) := s1 ∩ s2.
Definition set_union {A} (s1 s2: set A) := s1 ∪ s2.
Definition set_empty {A}: set A := ∅.
Definition set_singleton {A} (x: A): set A := {[ x ]}.
Definition set_elem_of {A} (x: A) (s: set A): bool := propInBool (x ∈ s).

Hint Unfold set_intersection.
Hint Unfold set_elem_of.
Hint Unfold set_union.
Hint Unfold set_subset.
Hint Unfold set_equality.
Hint Unfold set_empty.
Hint Unfold set_singleton.
Hint Unfold set_difference.

Lemma coqToSetEquality:
  forall {T} (a b: set T), a = b -> a ≡ b.
Proof.
  set_solver.
Qed.


Lemma union_empty_l_eq:
  forall T (s: set T), s ∪ ∅ ≡ s.
Proof.
  intros. set_solver.
Qed.

Lemma union_empty_r_eq:
  forall {T} (s: set T), ∅ ∪ s ≡ s.
Proof.
  intros. set_solver. 
Qed.


Lemma union_empty_l:
  forall T (s: set T), s ∪ ∅ = s.
Admitted.

Lemma union_empty_r:
  forall T (s: set T), ∅ ∪ s = s.
Admitted.


Hint Resolve union_empty_l union_empty_r: sets.


Lemma union_equals_eq:
  forall {T} (s1 s2 s3: set T),
    s2 ≡ s3 -> s1 ∪ s2 ≡ s1 ∪ s3.
Proof.
  intros; set_solver.
Qed.


Lemma union_equals:
  forall {T} (s1 s2 s3: set T),
    s2 ≡ s3 -> s1 ∪ s2 ≡ s1 ∪ s3. 
Proof.
  intros; set_solver.
Qed.
  
Lemma subs_eq:
  forall T (s1 s2: set T),
    s1 ≡ s2 <-> s1 ⊆ s2 /\ s2 ⊆ s1.
Proof.
  intros; set_solver.
Qed.

Lemma union_left:
  forall T (s1 s2 s3: set T),
    s1 ∪ s2 ⊆ s3 <-> (s1 ⊆ s3 /\ s2 ⊆ s3).
Proof.
  intros; set_solver.
Qed.

Lemma intersection_right:
  forall T (s1 s2 s3: set T),
    s1 ⊆ s2 ∩ s3 <-> (s1 ⊆ s2 /\ s1 ⊆ s3).
Proof.
  intros; set_solver.
Qed.
(*
Lemma union_contains: 
  forall {T} (x: T) (s1 s2: set T),
    (x ∈ s1) \/ (x ∈ s2) <-> x ∈ (s1 ∪ s2).
Proof.
  intros. set_solver.
Qed.
*)


Lemma empty_subset:
  forall T (s: set T),
    ∅ ⊆ s.
Proof.
  set_solver.
Qed.
  
Hint Resolve empty_subset: b_sets.

  Hint Rewrite union_empty_l: libSet.
Hint Rewrite union_empty_r: libSet.
Hint Rewrite subs_eq: libSet.
Hint Rewrite union_left: libSet.
Hint Rewrite intersection_right: libSet.

Ltac t_sets :=
  match goal with
  | _ => apply union_equals_eq
  | H: ?a = ?b |- _ =>
    poseNew (Mark (a,b) "coqToSetEquality");
    poseNew (coqToSetEquality _ _ H)
  | _ => set_solver
  | _ => apply False_ind; set_solver
  end; auto 1 with b_sets.
