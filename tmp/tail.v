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

Ltac t609 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t610 :=
  t609 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t610.


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

Lemma None_exists: (forall T: Type, forall self464: Option T, ((true = isNone T self464)) <-> (((None_construct T = self464)))). 
Proof.
	repeat t610 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self465: Option T, ((true = isSome T self465)) <-> ((exists tmp174: T, (Some_construct T tmp174 = self465)))). 
Proof.
	repeat t610 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic58 := match goal with 
	| [ H232: (true = isNone ?T ?self466) |- _ ] => 
			poseNew (Mark (T,self466) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H232)
	| [ H232: (isNone ?T ?self466 = true) |- _ ] => 
			poseNew (Mark (T,self466) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H232))
	| [ H233: (true = isSome ?T ?self467) |- _ ] => 
			poseNew (Mark (T,self467) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H233)
	| [ H233: (isSome ?T ?self467 = true) |- _ ] => 
			poseNew (Mark (T,self467) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H233))
	| _ => idtac
end.

Ltac t611 :=
  t_base ||
  Option_tactic58 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t612 :=
  t611 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t612.


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

Lemma Cons_exists: (forall T: Type, forall self468: List T, ((true = isCons T self468)) <-> ((exists tmp176: List T, exists tmp175: T, (Cons_construct T tmp175 tmp176 = self468)))). 
Proof.
	repeat t612 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self469: List T, ((true = isNil T self469)) <-> (((Nil_construct T = self469)))). 
Proof.
	repeat t612 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic58 := match goal with 
	| [ H234: (true = isCons ?T ?self470) |- _ ] => 
			poseNew (Mark (T,self470) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H234)
	| [ H234: (isCons ?T ?self470 = true) |- _ ] => 
			poseNew (Mark (T,self470) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H234))
	| [ H235: (true = isNil ?T ?self471) |- _ ] => 
			poseNew (Mark (T,self471) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H235)
	| [ H235: (isNil ?T ?self471 = true) |- _ ] => 
			poseNew (Mark (T,self471) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H235))
	| _ => Option_tactic58
end.

Ltac t613 :=
  t_base ||
  List_tactic58 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t614 :=
  t613 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t614.

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
  Start of tail
 ***********************)

Definition tail (T: Type) (thiss56: List T) (contractHyp175: (negb (propInBool ((thiss56 = Nil_construct T))) = true)) : List T :=
ifthenelse (isCons _ thiss56) (List T)
	(fun _ => t7 T thiss56 )
	(fun _ => let contradiction: False := _ in match contradiction with end ).

Fail Next Obligation.

Hint Unfold tail: definitions.

(***********************
  End of tail
 ***********************)
