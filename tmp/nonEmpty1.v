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

Ltac t201 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t202 :=
  t201 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t202.


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

Lemma None_exists: (forall T: Type, forall self208: Option T, ((true = isNone T self208)) <-> (((None_construct T = self208)))). 
Proof.
	repeat t202 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self209: Option T, ((true = isSome T self209)) <-> ((exists tmp78: T, (Some_construct T tmp78 = self209)))). 
Proof.
	repeat t202 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic26 := match goal with 
	| [ H104: (true = isNone ?T ?self210) |- _ ] => 
			poseNew (Mark (T,self210) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H104)
	| [ H104: (isNone ?T ?self210 = true) |- _ ] => 
			poseNew (Mark (T,self210) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H104))
	| [ H105: (true = isSome ?T ?self211) |- _ ] => 
			poseNew (Mark (T,self211) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H105)
	| [ H105: (isSome ?T ?self211 = true) |- _ ] => 
			poseNew (Mark (T,self211) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H105))
	| _ => idtac
end.

Ltac t203 :=
  t_base ||
  Option_tactic26 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t204 :=
  t203 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t204.


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

Lemma Cons_exists: (forall T: Type, forall self212: List T, ((true = isCons T self212)) <-> ((exists tmp80: List T, exists tmp79: T, (Cons_construct T tmp79 tmp80 = self212)))). 
Proof.
	repeat t204 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self213: List T, ((true = isNil T self213)) <-> (((Nil_construct T = self213)))). 
Proof.
	repeat t204 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic26 := match goal with 
	| [ H106: (true = isCons ?T ?self214) |- _ ] => 
			poseNew (Mark (T,self214) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H106)
	| [ H106: (isCons ?T ?self214 = true) |- _ ] => 
			poseNew (Mark (T,self214) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H106))
	| [ H107: (true = isNil ?T ?self215) |- _ ] => 
			poseNew (Mark (T,self215) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H107)
	| [ H107: (isNil ?T ?self215 = true) |- _ ] => 
			poseNew (Mark (T,self215) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H107))
	| _ => Option_tactic26
end.

Ltac t205 :=
  t_base ||
  List_tactic26 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t206 :=
  t205 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t206.

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
  Start of nonEmpty
 ***********************)

Definition nonEmpty1 (T: Type) (thiss25: Option T) : bool :=
negb (isEmpty1 T thiss25).

Fail Next Obligation.

Hint Unfold nonEmpty1: definitions.

(***********************
  End of nonEmpty
 ***********************)
