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

Ltac t152 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t153 :=
  t152 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t153.


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

Lemma None_exists: (forall T: Type, forall self152: Option T, ((true = isNone T self152)) <-> (((None_construct T = self152)))). 
Proof.
	repeat t153 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self153: Option T, ((true = isSome T self153)) <-> ((exists tmp57: T, (Some_construct T tmp57 = self153)))). 
Proof.
	repeat t153 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic19 := match goal with 
	| [ H76: (true = isNone ?T ?self154) |- _ ] => 
			poseNew (Mark (T,self154) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H76)
	| [ H76: (isNone ?T ?self154 = true) |- _ ] => 
			poseNew (Mark (T,self154) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H76))
	| [ H77: (true = isSome ?T ?self155) |- _ ] => 
			poseNew (Mark (T,self155) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H77)
	| [ H77: (isSome ?T ?self155 = true) |- _ ] => 
			poseNew (Mark (T,self155) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H77))
	| _ => idtac
end.

Ltac t154 :=
  t_base ||
  Option_tactic19 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t155 :=
  t154 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t155.


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

Lemma Cons_exists: (forall T: Type, forall self156: List T, ((true = isCons T self156)) <-> ((exists tmp59: List T, exists tmp58: T, (Cons_construct T tmp58 tmp59 = self156)))). 
Proof.
	repeat t155 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self157: List T, ((true = isNil T self157)) <-> (((Nil_construct T = self157)))). 
Proof.
	repeat t155 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic19 := match goal with 
	| [ H78: (true = isCons ?T ?self158) |- _ ] => 
			poseNew (Mark (T,self158) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H78)
	| [ H78: (isCons ?T ?self158 = true) |- _ ] => 
			poseNew (Mark (T,self158) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H78))
	| [ H79: (true = isNil ?T ?self159) |- _ ] => 
			poseNew (Mark (T,self159) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H79)
	| [ H79: (isNil ?T ?self159 = true) |- _ ] => 
			poseNew (Mark (T,self159) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H79))
	| _ => Option_tactic19
end.

Ltac t156 :=
  t_base ||
  List_tactic19 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t157 :=
  t156 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t157.

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
