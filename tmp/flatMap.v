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

Ltac t52 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t53 :=
  t52 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t53.


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

Lemma None_exists: (forall T: Type, forall self48: Option T, ((true = isNone T self48)) <-> (((None_construct T = self48)))). 
Proof.
	repeat t53 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self49: Option T, ((true = isSome T self49)) <-> ((exists tmp18: T, (Some_construct T tmp18 = self49)))). 
Proof.
	repeat t53 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic6 := match goal with 
	| [ H24: (true = isNone ?T ?self50) |- _ ] => 
			poseNew (Mark (T,self50) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H24)
	| [ H24: (isNone ?T ?self50 = true) |- _ ] => 
			poseNew (Mark (T,self50) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H24))
	| [ H25: (true = isSome ?T ?self51) |- _ ] => 
			poseNew (Mark (T,self51) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H25)
	| [ H25: (isSome ?T ?self51 = true) |- _ ] => 
			poseNew (Mark (T,self51) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H25))
	| _ => idtac
end.

Ltac t54 :=
  t_base ||
  Option_tactic6 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t55 :=
  t54 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t55.


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

Lemma Cons_exists: (forall T: Type, forall self52: List T, ((true = isCons T self52)) <-> ((exists tmp20: List T, exists tmp19: T, (Cons_construct T tmp19 tmp20 = self52)))). 
Proof.
	repeat t55 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self53: List T, ((true = isNil T self53)) <-> (((Nil_construct T = self53)))). 
Proof.
	repeat t55 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic6 := match goal with 
	| [ H26: (true = isCons ?T ?self54) |- _ ] => 
			poseNew (Mark (T,self54) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H26)
	| [ H26: (isCons ?T ?self54 = true) |- _ ] => 
			poseNew (Mark (T,self54) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H26))
	| [ H27: (true = isNil ?T ?self55) |- _ ] => 
			poseNew (Mark (T,self55) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H27)
	| [ H27: (isNil ?T ?self55 = true) |- _ ] => 
			poseNew (Mark (T,self55) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H27))
	| _ => Option_tactic6
end.

Ltac t56 :=
  t_base ||
  List_tactic6 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t57 :=
  t56 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t57.

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
  Start of flatMap
 ***********************)

Definition flatMap (T: Type) (R: Type) (thiss5: Option T) (f: T -> (Option R)) : Option R :=
match thiss5 with
| None_construct _ => None_construct R
| Some_construct _ x => f x
end.

Fail Next Obligation.

Hint Unfold flatMap: definitions.

(***********************
  End of flatMap
 ***********************)
