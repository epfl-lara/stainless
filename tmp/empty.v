Require Import SLC.Lib.
Require Import SLC.PropBool.
Require Import SLC.Booleans.
Require Import SLC.Sets.
Require Import SLC.Tactics.
Require Import SLC.Ints.
Require Import SLC.Unfolding.
Require Import ZArith.
Set Program Mode.

Opaque set_elem_of.
Opaque set_union.
Opaque set_intersection.
Opaque set_subset.
Opaque set_empty.
Opaque set_singleton.
Opaque set_difference.

Ltac t29 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t30 :=
  t29 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t30.


Inductive Option (T: Type) :=
| None_construct: Option T
| Some_construct: T -> (Option T).

Definition isNone (T: Type) (src: Option T) : bool :=
match src with
| None_construct _ => true
| _ => false
end.

Fail Next Obligation.

Hint Unfold  isNone: recognizers. 

Definition isSome (T: Type) (src: Option T) : bool :=
match src with
| Some_construct _ _ => true
| _ => false
end.

Fail Next Obligation.

Hint Unfold  isSome: recognizers. 

Lemma None_exists: (forall T: Type, forall self24: Option T, ((true = isNone T self24)) <-> (((None_construct T = self24)))). 
Proof.
	repeat t30 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self25: Option T, ((true = isSome T self25)) <-> ((exists tmp9: T, (Some_construct T tmp9 = self25)))). 
Proof.
	repeat t30 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic3 := match goal with 
	| [ H12: (true = isNone ?T ?self26) |- _ ] => 
			poseNew (Mark (T,self26) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H12)
	| [ H12: (isNone ?T ?self26 = true) |- _ ] => 
			poseNew (Mark (T,self26) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H12))
	| [ H13: (true = isSome ?T ?self27) |- _ ] => 
			poseNew (Mark (T,self27) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H13)
	| [ H13: (isSome ?T ?self27 = true) |- _ ] => 
			poseNew (Mark (T,self27) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H13))
	| _ => idtac
end.

Ltac t31 :=
  t_base ||
  Option_tactic3 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t32 :=
  t31 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t32.


Definition v (T: Type) (src: Some_type T) : T :=
match src with
| Some_construct _ f0 => f0
| _ => let contradiction: False := _ in match contradiction with end
end.

Fail Next Obligation.

Inductive List (T: Type) :=
| Cons_construct: T -> ((List T) -> (List T))
| Nil_construct: List T.

Definition isCons (T: Type) (src: List T) : bool :=
match src with
| Cons_construct _ _ _ => true
| _ => false
end.

Fail Next Obligation.

Hint Unfold  isCons: recognizers. 

Definition isNil (T: Type) (src: List T) : bool :=
match src with
| Nil_construct _ => true
| _ => false
end.

Fail Next Obligation.

Hint Unfold  isNil: recognizers. 

Lemma Cons_exists: (forall T: Type, forall self28: List T, ((true = isCons T self28)) <-> ((exists tmp11: List T, exists tmp10: T, (Cons_construct T tmp10 tmp11 = self28)))). 
Proof.
	repeat t32 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self29: List T, ((true = isNil T self29)) <-> (((Nil_construct T = self29)))). 
Proof.
	repeat t32 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic3 := match goal with 
	| [ H14: (true = isCons ?T ?self30) |- _ ] => 
			poseNew (Mark (T,self30) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H14)
	| [ H14: (isCons ?T ?self30 = true) |- _ ] => 
			poseNew (Mark (T,self30) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H14))
	| [ H15: (true = isNil ?T ?self31) |- _ ] => 
			poseNew (Mark (T,self31) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H15)
	| [ H15: (isNil ?T ?self31 = true) |- _ ] => 
			poseNew (Mark (T,self31) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H15))
	| _ => Option_tactic3
end.

Ltac t33 :=
  t_base ||
  List_tactic3 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t34 :=
  t33 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t34.

Definition h (T: Type) (src: Cons_type T) : T :=
match src with
| Cons_construct _ f0 f1 => f0
| _ => let contradiction: False := _ in match contradiction with end
end.

Fail Next Obligation.

Definition t7 (T: Type) (src: Cons_type T) : List T :=
match src with
| Cons_construct _ f0 f1 => f1
| _ => let contradiction: False := _ in match contradiction with end
end.

Fail Next Obligation.



(***********************
  Start of empty
 ***********************)

Definition empty (A: Type) (B: Type) : map_type A (Option B) :=
magic (map_type A (Option B)).

Fail Next Obligation.

Hint Unfold empty: definitions.

(***********************
  End of empty
 ***********************)
