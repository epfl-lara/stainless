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

Ltac t1 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t2 :=
  t1 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t2.


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

Lemma None_exists: (forall T: Type, forall self: Option T, ((true = isNone T self)) <-> (((None_construct T = self)))). 
Proof.
	repeat t2 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self1: Option T, ((true = isSome T self1)) <-> ((exists tmp: T, (Some_construct T tmp = self1)))). 
Proof.
	repeat t2 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic := match goal with 
	| [ H: (true = isNone ?T ?self2) |- _ ] => 
			poseNew (Mark (T,self2) "None_exists");pose proof ((proj1 (None_exists _ _)) H)
	| [ H: (isNone ?T ?self2 = true) |- _ ] => 
			poseNew (Mark (T,self2) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H))
	| [ H1: (true = isSome ?T ?self3) |- _ ] => 
			poseNew (Mark (T,self3) "Some_exists");pose proof ((proj1 (Some_exists _ _)) H1)
	| [ H1: (isSome ?T ?self3 = true) |- _ ] => 
			poseNew (Mark (T,self3) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H1))
	| _ => idtac
end.

Ltac t3 :=
  t_base ||
  Option_tactic ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t4 :=
  t3 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t4.


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

Lemma Cons_exists: (forall T: Type, forall self4: List T, ((true = isCons T self4)) <-> ((exists tmp2: List T, exists tmp1: T, (Cons_construct T tmp1 tmp2 = self4)))). 
Proof.
	repeat t4 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self5: List T, ((true = isNil T self5)) <-> (((Nil_construct T = self5)))). 
Proof.
	repeat t4 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic := match goal with 
	| [ H2: (true = isCons ?T ?self6) |- _ ] => 
			poseNew (Mark (T,self6) "Cons_exists");pose proof ((proj1 (Cons_exists _ _)) H2)
	| [ H2: (isCons ?T ?self6 = true) |- _ ] => 
			poseNew (Mark (T,self6) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H2))
	| [ H3: (true = isNil ?T ?self7) |- _ ] => 
			poseNew (Mark (T,self7) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H3)
	| [ H3: (isNil ?T ?self7 = true) |- _ ] => 
			poseNew (Mark (T,self7) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H3))
	| _ => Option_tactic
end.

Ltac t5 :=
  t_base ||
  List_tactic ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t6 :=
  t5 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t6.

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
  Start of ::
 ***********************)

Definition cons_ (T: Type) (thiss: List T) (t8: T) : List T :=
Cons_construct T t8 thiss.

Fail Next Obligation.

Hint Unfold cons_: definitions.

(***********************
  End of ::
 ***********************)
