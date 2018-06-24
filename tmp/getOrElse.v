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

Ltac t105 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t106 :=
  t105 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t106.


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

Lemma None_exists: (forall T: Type, forall self104: Option T, ((true = isNone T self104)) <-> (((None_construct T = self104)))). 
Proof.
	repeat t106 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self105: Option T, ((true = isSome T self105)) <-> ((exists tmp39: T, (Some_construct T tmp39 = self105)))). 
Proof.
	repeat t106 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic13 := match goal with 
	| [ H52: (true = isNone ?T ?self106) |- _ ] => 
			poseNew (Mark (T,self106) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H52)
	| [ H52: (isNone ?T ?self106 = true) |- _ ] => 
			poseNew (Mark (T,self106) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H52))
	| [ H53: (true = isSome ?T ?self107) |- _ ] => 
			poseNew (Mark (T,self107) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H53)
	| [ H53: (isSome ?T ?self107 = true) |- _ ] => 
			poseNew (Mark (T,self107) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H53))
	| _ => idtac
end.

Ltac t107 :=
  t_base ||
  Option_tactic13 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t108 :=
  t107 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t108.


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

Lemma Cons_exists: (forall T: Type, forall self108: List T, ((true = isCons T self108)) <-> ((exists tmp41: List T, exists tmp40: T, (Cons_construct T tmp40 tmp41 = self108)))). 
Proof.
	repeat t108 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self109: List T, ((true = isNil T self109)) <-> (((Nil_construct T = self109)))). 
Proof.
	repeat t108 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic13 := match goal with 
	| [ H54: (true = isCons ?T ?self110) |- _ ] => 
			poseNew (Mark (T,self110) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H54)
	| [ H54: (isCons ?T ?self110 = true) |- _ ] => 
			poseNew (Mark (T,self110) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H54))
	| [ H55: (true = isNil ?T ?self111) |- _ ] => 
			poseNew (Mark (T,self111) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H55)
	| [ H55: (isNil ?T ?self111 = true) |- _ ] => 
			poseNew (Mark (T,self111) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H55))
	| _ => Option_tactic13
end.

Ltac t109 :=
  t_base ||
  List_tactic13 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t110 :=
  t109 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t110.

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
  Start of getOrElse
 ***********************)

Definition getOrElse (T: Type) (thiss12: Option T) (default: T) : T :=
match thiss12 with
| Some_construct _ v2 => v2
| None_construct _ => default
end.

Fail Next Obligation.

Hint Unfold getOrElse: definitions.

(***********************
  End of getOrElse
 ***********************)
