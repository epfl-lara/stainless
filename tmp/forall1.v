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

Ltac t93 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t94 :=
  t93 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t94.


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

Lemma None_exists: (forall T: Type, forall self88: Option T, ((true = isNone T self88)) <-> (((None_construct T = self88)))). 
Proof.
	repeat t94 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self89: Option T, ((true = isSome T self89)) <-> ((exists tmp33: T, (Some_construct T tmp33 = self89)))). 
Proof.
	repeat t94 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic11 := match goal with 
	| [ H44: (true = isNone ?T ?self90) |- _ ] => 
			poseNew (Mark (T,self90) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H44)
	| [ H44: (isNone ?T ?self90 = true) |- _ ] => 
			poseNew (Mark (T,self90) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H44))
	| [ H45: (true = isSome ?T ?self91) |- _ ] => 
			poseNew (Mark (T,self91) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H45)
	| [ H45: (isSome ?T ?self91 = true) |- _ ] => 
			poseNew (Mark (T,self91) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H45))
	| _ => idtac
end.

Ltac t95 :=
  t_base ||
  Option_tactic11 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t96 :=
  t95 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t96.


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

Lemma Cons_exists: (forall T: Type, forall self92: List T, ((true = isCons T self92)) <-> ((exists tmp35: List T, exists tmp34: T, (Cons_construct T tmp34 tmp35 = self92)))). 
Proof.
	repeat t96 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self93: List T, ((true = isNil T self93)) <-> (((Nil_construct T = self93)))). 
Proof.
	repeat t96 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic11 := match goal with 
	| [ H46: (true = isCons ?T ?self94) |- _ ] => 
			poseNew (Mark (T,self94) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H46)
	| [ H46: (isCons ?T ?self94 = true) |- _ ] => 
			poseNew (Mark (T,self94) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H46))
	| [ H47: (true = isNil ?T ?self95) |- _ ] => 
			poseNew (Mark (T,self95) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H47)
	| [ H47: (isNil ?T ?self95 = true) |- _ ] => 
			poseNew (Mark (T,self95) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H47))
	| _ => Option_tactic11
end.

Ltac t97 :=
  t_base ||
  List_tactic11 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t98 :=
  t97 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t98.

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
  Start of forall
 ***********************)

Definition forall1 (T: Type) (thiss10: Option T) (p4: T -> bool) : bool :=
ifthenelse
	(ifthenelse (isSome _ thiss10) bool
		(fun _ => negb (p4 (v T thiss10)) )
		(fun _ => false ))
	bool
	(fun _ => false )
	(fun _ => true ).

Fail Next Obligation.

Hint Unfold forall1: definitions.

(***********************
  End of forall
 ***********************)
