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

Ltac t35 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t36 :=
  t35 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t36.


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

Lemma None_exists: (forall T: Type, forall self32: Option T, ((true = isNone T self32)) <-> (((None_construct T = self32)))). 
Proof.
	repeat t36 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self33: Option T, ((true = isSome T self33)) <-> ((exists tmp12: T, (Some_construct T tmp12 = self33)))). 
Proof.
	repeat t36 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic4 := match goal with 
	| [ H16: (true = isNone ?T ?self34) |- _ ] => 
			poseNew (Mark (T,self34) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H16)
	| [ H16: (isNone ?T ?self34 = true) |- _ ] => 
			poseNew (Mark (T,self34) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H16))
	| [ H17: (true = isSome ?T ?self35) |- _ ] => 
			poseNew (Mark (T,self35) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H17)
	| [ H17: (isSome ?T ?self35 = true) |- _ ] => 
			poseNew (Mark (T,self35) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H17))
	| _ => idtac
end.

Ltac t37 :=
  t_base ||
  Option_tactic4 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t38 :=
  t37 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t38.


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

Lemma Cons_exists: (forall T: Type, forall self36: List T, ((true = isCons T self36)) <-> ((exists tmp14: List T, exists tmp13: T, (Cons_construct T tmp13 tmp14 = self36)))). 
Proof.
	repeat t38 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self37: List T, ((true = isNil T self37)) <-> (((Nil_construct T = self37)))). 
Proof.
	repeat t38 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic4 := match goal with 
	| [ H18: (true = isCons ?T ?self38) |- _ ] => 
			poseNew (Mark (T,self38) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H18)
	| [ H18: (isCons ?T ?self38 = true) |- _ ] => 
			poseNew (Mark (T,self38) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H18))
	| [ H19: (true = isNil ?T ?self39) |- _ ] => 
			poseNew (Mark (T,self39) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H19)
	| [ H19: (isNil ?T ?self39 = true) |- _ ] => 
			poseNew (Mark (T,self39) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H19))
	| _ => Option_tactic4
end.

Ltac t39 :=
  t_base ||
  List_tactic4 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t40 :=
  t39 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t40.

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
  Start of filter
 ***********************)

Definition filter (T: Type) (thiss3: Option T) (p: T -> bool) : Option T :=
ifthenelse
	(ifthenelse (isSome _ thiss3) bool
		(fun _ => p (v T thiss3) )
		(fun _ => false ))
	(Option T)
	(fun _ => Some_construct T (v T thiss3) )
	(fun _ => None_construct T ).

Fail Next Obligation.

Hint Unfold filter: definitions.

(***********************
  End of filter
 ***********************)
