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

Ltac t195 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t196 :=
  t195 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t196.


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

Lemma None_exists: (forall T: Type, forall self200: Option T, ((true = isNone T self200)) <-> (((None_construct T = self200)))). 
Proof.
	repeat t196 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self201: Option T, ((true = isSome T self201)) <-> ((exists tmp75: T, (Some_construct T tmp75 = self201)))). 
Proof.
	repeat t196 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic25 := match goal with 
	| [ H100: (true = isNone ?T ?self202) |- _ ] => 
			poseNew (Mark (T,self202) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H100)
	| [ H100: (isNone ?T ?self202 = true) |- _ ] => 
			poseNew (Mark (T,self202) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H100))
	| [ H101: (true = isSome ?T ?self203) |- _ ] => 
			poseNew (Mark (T,self203) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H101)
	| [ H101: (isSome ?T ?self203 = true) |- _ ] => 
			poseNew (Mark (T,self203) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H101))
	| _ => idtac
end.

Ltac t197 :=
  t_base ||
  Option_tactic25 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t198 :=
  t197 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t198.


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

Lemma Cons_exists: (forall T: Type, forall self204: List T, ((true = isCons T self204)) <-> ((exists tmp77: List T, exists tmp76: T, (Cons_construct T tmp76 tmp77 = self204)))). 
Proof.
	repeat t198 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self205: List T, ((true = isNil T self205)) <-> (((Nil_construct T = self205)))). 
Proof.
	repeat t198 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic25 := match goal with 
	| [ H102: (true = isCons ?T ?self206) |- _ ] => 
			poseNew (Mark (T,self206) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H102)
	| [ H102: (isCons ?T ?self206 = true) |- _ ] => 
			poseNew (Mark (T,self206) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H102))
	| [ H103: (true = isNil ?T ?self207) |- _ ] => 
			poseNew (Mark (T,self207) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H103)
	| [ H103: (isNil ?T ?self207 = true) |- _ ] => 
			poseNew (Mark (T,self207) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H103))
	| _ => Option_tactic25
end.

Ltac t199 :=
  t_base ||
  List_tactic25 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t200 :=
  t199 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t200.

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
  Start of nonEmpty
 ***********************)

Definition nonEmpty (T: Type) (thiss24: List T) : bool :=
negb (isEmpty T thiss24).

Fail Next Obligation.

Hint Unfold nonEmpty: definitions.

(***********************
  End of nonEmpty
 ***********************)
