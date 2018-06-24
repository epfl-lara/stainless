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

Ltac t164 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t165 :=
  t164 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t165.


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

Lemma None_exists: (forall T: Type, forall self168: Option T, ((true = isNone T self168)) <-> (((None_construct T = self168)))). 
Proof.
	repeat t165 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self169: Option T, ((true = isSome T self169)) <-> ((exists tmp63: T, (Some_construct T tmp63 = self169)))). 
Proof.
	repeat t165 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic21 := match goal with 
	| [ H84: (true = isNone ?T ?self170) |- _ ] => 
			poseNew (Mark (T,self170) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H84)
	| [ H84: (isNone ?T ?self170 = true) |- _ ] => 
			poseNew (Mark (T,self170) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H84))
	| [ H85: (true = isSome ?T ?self171) |- _ ] => 
			poseNew (Mark (T,self171) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H85)
	| [ H85: (isSome ?T ?self171 = true) |- _ ] => 
			poseNew (Mark (T,self171) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H85))
	| _ => idtac
end.

Ltac t166 :=
  t_base ||
  Option_tactic21 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t167 :=
  t166 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t167.


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

Lemma Cons_exists: (forall T: Type, forall self172: List T, ((true = isCons T self172)) <-> ((exists tmp65: List T, exists tmp64: T, (Cons_construct T tmp64 tmp65 = self172)))). 
Proof.
	repeat t167 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self173: List T, ((true = isNil T self173)) <-> (((Nil_construct T = self173)))). 
Proof.
	repeat t167 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic21 := match goal with 
	| [ H86: (true = isCons ?T ?self174) |- _ ] => 
			poseNew (Mark (T,self174) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H86)
	| [ H86: (isCons ?T ?self174 = true) |- _ ] => 
			poseNew (Mark (T,self174) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H86))
	| [ H87: (true = isNil ?T ?self175) |- _ ] => 
			poseNew (Mark (T,self175) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H87)
	| [ H87: (isNil ?T ?self175 = true) |- _ ] => 
			poseNew (Mark (T,self175) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H87))
	| _ => Option_tactic21
end.

Ltac t168 :=
  t_base ||
  List_tactic21 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t169 :=
  t168 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t169.

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
  Start of get
 ***********************)

Definition get (T: Type) (thiss20: Option T) (contractHyp33: (isDefined T thiss20 = true)) : T :=
ifthenelse (isSome _ thiss20) T
	(fun _ => v T thiss20 )
	(fun _ => let contradiction: False := _ in match contradiction with end ).

Fail Next Obligation.

Hint Unfold get: definitions.

(***********************
  End of get
 ***********************)
