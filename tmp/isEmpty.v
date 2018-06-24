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

Ltac t146 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t147 :=
  t146 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t147.


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

Lemma None_exists: (forall T: Type, forall self144: Option T, ((true = isNone T self144)) <-> (((None_construct T = self144)))). 
Proof.
	repeat t147 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self145: Option T, ((true = isSome T self145)) <-> ((exists tmp54: T, (Some_construct T tmp54 = self145)))). 
Proof.
	repeat t147 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic18 := match goal with 
	| [ H72: (true = isNone ?T ?self146) |- _ ] => 
			poseNew (Mark (T,self146) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H72)
	| [ H72: (isNone ?T ?self146 = true) |- _ ] => 
			poseNew (Mark (T,self146) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H72))
	| [ H73: (true = isSome ?T ?self147) |- _ ] => 
			poseNew (Mark (T,self147) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H73)
	| [ H73: (isSome ?T ?self147 = true) |- _ ] => 
			poseNew (Mark (T,self147) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H73))
	| _ => idtac
end.

Ltac t148 :=
  t_base ||
  Option_tactic18 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t149 :=
  t148 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t149.


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

Lemma Cons_exists: (forall T: Type, forall self148: List T, ((true = isCons T self148)) <-> ((exists tmp56: List T, exists tmp55: T, (Cons_construct T tmp55 tmp56 = self148)))). 
Proof.
	repeat t149 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self149: List T, ((true = isNil T self149)) <-> (((Nil_construct T = self149)))). 
Proof.
	repeat t149 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic18 := match goal with 
	| [ H74: (true = isCons ?T ?self150) |- _ ] => 
			poseNew (Mark (T,self150) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H74)
	| [ H74: (isCons ?T ?self150 = true) |- _ ] => 
			poseNew (Mark (T,self150) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H74))
	| [ H75: (true = isNil ?T ?self151) |- _ ] => 
			poseNew (Mark (T,self151) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H75)
	| [ H75: (isNil ?T ?self151 = true) |- _ ] => 
			poseNew (Mark (T,self151) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H75))
	| _ => Option_tactic18
end.

Ltac t150 :=
  t_base ||
  List_tactic18 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t151 :=
  t150 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t151.

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
