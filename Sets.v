Definition set A := A -> Prop.

Definition set_intersection {A} (s1 s2 : set A) x := s1 x /\ s2 x.

Definition set_union {A} (s1 s2 : set A) x := s1 x \/ s2 x.

Definition set_mem {A} (s: set A) x := s x.

Definition set_subset {A} (s1 s2 : set A) x := s1 x -> s2 x.

Definition set_equality {A} (s1 s2 : set A) x := s1 x <-> s2 x.

Definition set_difference {A} (s1 s2: set A) x := s1 x /\ ~(s2 x).

Notation "s1 '==' s2" := (set_equality s1 s2) (at level 50).


Hint Unfold set_intersection : sets.

Definition set_empty {A} (x: A) := False.
Definition set_singleton {A} (x y: A) := x = y.


Hint Unfold set_union : sets.
Hint Unfold set_mem : sets.
Hint Unfold set_subset : sets.
Hint Unfold set_equality : sets.
Hint Unfold set_empty : sets.
Hint Unfold set_singleton : sets.
Hint Unfold set_difference : sets.

