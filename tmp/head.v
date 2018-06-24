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

Ltac t120 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t121 :=
  t120 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t121.


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

Lemma None_exists: (forall T: Type, forall self120: Option T, ((true = isNone T self120)) <-> (((None_construct T = self120)))). 
Proof.
	repeat t121 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self121: Option T, ((true = isSome T self121)) <-> ((exists tmp45: T, (Some_construct T tmp45 = self121)))). 
Proof.
	repeat t121 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic15 := match goal with 
	| [ H60: (true = isNone ?T ?self122) |- _ ] => 
			poseNew (Mark (T,self122) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H60)
	| [ H60: (isNone ?T ?self122 = true) |- _ ] => 
			poseNew (Mark (T,self122) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H60))
	| [ H61: (true = isSome ?T ?self123) |- _ ] => 
			poseNew (Mark (T,self123) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H61)
	| [ H61: (isSome ?T ?self123 = true) |- _ ] => 
			poseNew (Mark (T,self123) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H61))
	| _ => idtac
end.

Ltac t122 :=
  t_base ||
  Option_tactic15 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t123 :=
  t122 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t123.


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

Lemma Cons_exists: (forall T: Type, forall self124: List T, ((true = isCons T self124)) <-> ((exists tmp47: List T, exists tmp46: T, (Cons_construct T tmp46 tmp47 = self124)))). 
Proof.
	repeat t123 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self125: List T, ((true = isNil T self125)) <-> (((Nil_construct T = self125)))). 
Proof.
	repeat t123 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic15 := match goal with 
	| [ H62: (true = isCons ?T ?self126) |- _ ] => 
			poseNew (Mark (T,self126) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H62)
	| [ H62: (isCons ?T ?self126 = true) |- _ ] => 
			poseNew (Mark (T,self126) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H62))
	| [ H63: (true = isNil ?T ?self127) |- _ ] => 
			poseNew (Mark (T,self127) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H63)
	| [ H63: (isNil ?T ?self127 = true) |- _ ] => 
			poseNew (Mark (T,self127) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H63))
	| _ => Option_tactic15
end.

Ltac t124 :=
  t_base ||
  List_tactic15 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t125 :=
  t124 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t125.

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
  Start of head
 ***********************)

Definition head (T: Type) (thiss14: List T) (contractHyp21: (negb (propInBool ((thiss14 = Nil_construct T))) = true)) : T :=
ifthenelse (isCons _ thiss14) T
	(fun _ => h T thiss14 )
	(fun _ => let contradiction: False := _ in match contradiction with end ).

Fail Next Obligation.

Hint Unfold head: definitions.

(***********************
  End of head
 ***********************)
