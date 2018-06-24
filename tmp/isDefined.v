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

Ltac t158 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t159 :=
  t158 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t159.


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

Lemma None_exists: (forall T: Type, forall self160: Option T, ((true = isNone T self160)) <-> (((None_construct T = self160)))). 
Proof.
	repeat t159 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self161: Option T, ((true = isSome T self161)) <-> ((exists tmp60: T, (Some_construct T tmp60 = self161)))). 
Proof.
	repeat t159 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic20 := match goal with 
	| [ H80: (true = isNone ?T ?self162) |- _ ] => 
			poseNew (Mark (T,self162) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H80)
	| [ H80: (isNone ?T ?self162 = true) |- _ ] => 
			poseNew (Mark (T,self162) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H80))
	| [ H81: (true = isSome ?T ?self163) |- _ ] => 
			poseNew (Mark (T,self163) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H81)
	| [ H81: (isSome ?T ?self163 = true) |- _ ] => 
			poseNew (Mark (T,self163) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H81))
	| _ => idtac
end.

Ltac t160 :=
  t_base ||
  Option_tactic20 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t161 :=
  t160 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t161.


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

Lemma Cons_exists: (forall T: Type, forall self164: List T, ((true = isCons T self164)) <-> ((exists tmp62: List T, exists tmp61: T, (Cons_construct T tmp61 tmp62 = self164)))). 
Proof.
	repeat t161 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self165: List T, ((true = isNil T self165)) <-> (((Nil_construct T = self165)))). 
Proof.
	repeat t161 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic20 := match goal with 
	| [ H82: (true = isCons ?T ?self166) |- _ ] => 
			poseNew (Mark (T,self166) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H82)
	| [ H82: (isCons ?T ?self166 = true) |- _ ] => 
			poseNew (Mark (T,self166) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H82))
	| [ H83: (true = isNil ?T ?self167) |- _ ] => 
			poseNew (Mark (T,self167) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H83)
	| [ H83: (isNil ?T ?self167 = true) |- _ ] => 
			poseNew (Mark (T,self167) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H83))
	| _ => Option_tactic20
end.

Ltac t162 :=
  t_base ||
  List_tactic20 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t163 :=
  t162 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t163.

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
