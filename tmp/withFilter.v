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

Ltac t792 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t793 :=
  t792 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t793.


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

Lemma None_exists: (forall T: Type, forall self592: Option T, ((true = isNone T self592)) <-> (((None_construct T = self592)))). 
Proof.
	repeat t793 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self593: Option T, ((true = isSome T self593)) <-> ((exists tmp222: T, (Some_construct T tmp222 = self593)))). 
Proof.
	repeat t793 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic74 := match goal with 
	| [ H296: (true = isNone ?T ?self594) |- _ ] => 
			poseNew (Mark (T,self594) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H296)
	| [ H296: (isNone ?T ?self594 = true) |- _ ] => 
			poseNew (Mark (T,self594) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H296))
	| [ H297: (true = isSome ?T ?self595) |- _ ] => 
			poseNew (Mark (T,self595) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H297)
	| [ H297: (isSome ?T ?self595 = true) |- _ ] => 
			poseNew (Mark (T,self595) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H297))
	| _ => idtac
end.

Ltac t794 :=
  t_base ||
  Option_tactic74 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t795 :=
  t794 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t795.


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

Lemma Cons_exists: (forall T: Type, forall self596: List T, ((true = isCons T self596)) <-> ((exists tmp224: List T, exists tmp223: T, (Cons_construct T tmp223 tmp224 = self596)))). 
Proof.
	repeat t795 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self597: List T, ((true = isNil T self597)) <-> (((Nil_construct T = self597)))). 
Proof.
	repeat t795 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic74 := match goal with 
	| [ H298: (true = isCons ?T ?self598) |- _ ] => 
			poseNew (Mark (T,self598) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H298)
	| [ H298: (isCons ?T ?self598 = true) |- _ ] => 
			poseNew (Mark (T,self598) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H298))
	| [ H299: (true = isNil ?T ?self599) |- _ ] => 
			poseNew (Mark (T,self599) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H299)
	| [ H299: (isNil ?T ?self599 = true) |- _ ] => 
			poseNew (Mark (T,self599) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H299))
	| _ => Option_tactic74
end.

Ltac t796 :=
  t_base ||
  List_tactic74 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t797 :=
  t796 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t797.

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


(***********************
  Start of withFilter
 ***********************)

Definition withFilter (T: Type) (thiss71: Option T) (p13: T -> bool) : Option T :=
filter T thiss71 p13.

Fail Next Obligation.

Hint Unfold withFilter: definitions.

(***********************
  End of withFilter
 ***********************)
