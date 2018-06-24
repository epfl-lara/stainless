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

Ltac t189 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t190 :=
  t189 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t190.


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

Lemma None_exists: (forall T: Type, forall self192: Option T, ((true = isNone T self192)) <-> (((None_construct T = self192)))). 
Proof.
	repeat t190 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self193: Option T, ((true = isSome T self193)) <-> ((exists tmp72: T, (Some_construct T tmp72 = self193)))). 
Proof.
	repeat t190 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic24 := match goal with 
	| [ H96: (true = isNone ?T ?self194) |- _ ] => 
			poseNew (Mark (T,self194) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H96)
	| [ H96: (isNone ?T ?self194 = true) |- _ ] => 
			poseNew (Mark (T,self194) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H96))
	| [ H97: (true = isSome ?T ?self195) |- _ ] => 
			poseNew (Mark (T,self195) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H97)
	| [ H97: (isSome ?T ?self195 = true) |- _ ] => 
			poseNew (Mark (T,self195) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H97))
	| _ => idtac
end.

Ltac t191 :=
  t_base ||
  Option_tactic24 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t192 :=
  t191 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t192.


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

Lemma Cons_exists: (forall T: Type, forall self196: List T, ((true = isCons T self196)) <-> ((exists tmp74: List T, exists tmp73: T, (Cons_construct T tmp73 tmp74 = self196)))). 
Proof.
	repeat t192 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self197: List T, ((true = isNil T self197)) <-> (((Nil_construct T = self197)))). 
Proof.
	repeat t192 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic24 := match goal with 
	| [ H98: (true = isCons ?T ?self198) |- _ ] => 
			poseNew (Mark (T,self198) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H98)
	| [ H98: (isCons ?T ?self198 = true) |- _ ] => 
			poseNew (Mark (T,self198) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H98))
	| [ H99: (true = isNil ?T ?self199) |- _ ] => 
			poseNew (Mark (T,self199) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H99)
	| [ H99: (isNil ?T ?self199 = true) |- _ ] => 
			poseNew (Mark (T,self199) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H99))
	| _ => Option_tactic24
end.

Ltac t193 :=
  t_base ||
  List_tactic24 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t194 :=
  t193 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t194.

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
  Start of map
 ***********************)

Definition map (T: Type) (R: Type) (thiss23: Option T) (f4: T -> R) : {x___21: Option R | (Bool.eqb (isDefined R x___21) (isDefined T thiss23) = true)} :=
match thiss23 with
| None_construct _ => None_construct R
| Some_construct _ x1 => Some_construct R (f4 x1)
end.

Fail Next Obligation.

Hint Unfold map: definitions.

(***********************
  End of map
 ***********************)
