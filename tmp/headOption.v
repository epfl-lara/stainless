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

Ltac t170 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t171 :=
  t170 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t171.


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

Lemma None_exists: (forall T: Type, forall self176: Option T, ((true = isNone T self176)) <-> (((None_construct T = self176)))). 
Proof.
	repeat t171 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self177: Option T, ((true = isSome T self177)) <-> ((exists tmp66: T, (Some_construct T tmp66 = self177)))). 
Proof.
	repeat t171 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic22 := match goal with 
	| [ H88: (true = isNone ?T ?self178) |- _ ] => 
			poseNew (Mark (T,self178) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H88)
	| [ H88: (isNone ?T ?self178 = true) |- _ ] => 
			poseNew (Mark (T,self178) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H88))
	| [ H89: (true = isSome ?T ?self179) |- _ ] => 
			poseNew (Mark (T,self179) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H89)
	| [ H89: (isSome ?T ?self179 = true) |- _ ] => 
			poseNew (Mark (T,self179) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H89))
	| _ => idtac
end.

Ltac t172 :=
  t_base ||
  Option_tactic22 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t173 :=
  t172 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t173.


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

Lemma Cons_exists: (forall T: Type, forall self180: List T, ((true = isCons T self180)) <-> ((exists tmp68: List T, exists tmp67: T, (Cons_construct T tmp67 tmp68 = self180)))). 
Proof.
	repeat t173 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self181: List T, ((true = isNil T self181)) <-> (((Nil_construct T = self181)))). 
Proof.
	repeat t173 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic22 := match goal with 
	| [ H90: (true = isCons ?T ?self182) |- _ ] => 
			poseNew (Mark (T,self182) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H90)
	| [ H90: (isCons ?T ?self182 = true) |- _ ] => 
			poseNew (Mark (T,self182) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H90))
	| [ H91: (true = isNil ?T ?self183) |- _ ] => 
			poseNew (Mark (T,self183) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H91)
	| [ H91: (isNil ?T ?self183 = true) |- _ ] => 
			poseNew (Mark (T,self183) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H91))
	| _ => Option_tactic22
end.

Ltac t174 :=
  t_base ||
  List_tactic22 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t175 :=
  t174 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t175.

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
  Start of isEmpty
 ***********************)

Definition isEmpty (T: Type) (thiss17: List T) : bool :=
ifthenelse (isNil _ thiss17) bool
	(fun _ => true )
	(fun _ => false ).

Fail Next Obligation.

Hint Unfold isEmpty: definitions.

(***********************
  End of isEmpty
 ***********************)

(***********************
  Start of isEmpty
 ***********************)

Definition isEmpty1 (T: Type) (thiss18: Option T) : bool :=
propInBool ((thiss18 = None_construct T)).

Fail Next Obligation.

Hint Unfold isEmpty1: definitions.

(***********************
  End of isEmpty
 ***********************)

(***********************
  Start of isDefined
 ***********************)

Definition isDefined (T: Type) (thiss19: Option T) : bool :=
negb (isEmpty1 T thiss19).

Fail Next Obligation.

Hint Unfold isDefined: definitions.

(***********************
  End of isDefined
 ***********************)


(***********************
  Start of headOption
 ***********************)

Definition headOption (T: Type) (thiss21: List T) : {x___5: Option T | (negb (Bool.eqb (isDefined T x___5) (isEmpty T thiss21)) = true)} :=
match thiss21 with
| Cons_construct _ h8 t176 => Some_construct T h8
| Nil_construct _ => None_construct T
end.

Fail Next Obligation.

Hint Unfold headOption: definitions.

(***********************
  End of headOption
 ***********************)
