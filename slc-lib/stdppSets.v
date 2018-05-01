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
  
(*
Lemma union_empty_l:
  forall {T} (s: set T), set_union s set_empty = s.
Proof.
  intros; apply functional_extensionality; t_sets_aux.
Qed.

Lemma union_empty_r:
  forall {T} (s: set T), set_union set_empty s = s.
Proof.
  intros; apply functional_extensionality; t_sets_aux.
Qed.

Hint Resolve union_empty_l union_empty_r: sets. *)

Ltac t_sets :=
  match goal with
  | H: ?a = ?b |- _ =>
    poseNew (Mark (a,b) "coqToSetEquality");
    poseNew (coqToSetEquality _ _ H)
  | _ => set_solver
  | _ => apply False_ind; set_solver
  end.

Notation "'<' x '>'" := (exist _ x _).