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

Ltac t58 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t59 :=
  t58 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t59.


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

Lemma None_exists: (forall T: Type, forall self56: Option T, ((true = isNone T self56)) <-> (((None_construct T = self56)))). 
Proof.
	repeat t59 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self57: Option T, ((true = isSome T self57)) <-> ((exists tmp21: T, (Some_construct T tmp21 = self57)))). 
Proof.
	repeat t59 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic7 := match goal with 
	| [ H28: (true = isNone ?T ?self58) |- _ ] => 
			poseNew (Mark (T,self58) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H28)
	| [ H28: (isNone ?T ?self58 = true) |- _ ] => 
			poseNew (Mark (T,self58) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H28))
	| [ H29: (true = isSome ?T ?self59) |- _ ] => 
			poseNew (Mark (T,self59) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H29)
	| [ H29: (isSome ?T ?self59 = true) |- _ ] => 
			poseNew (Mark (T,self59) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H29))
	| _ => idtac
end.

Ltac t60 :=
  t_base ||
  Option_tactic7 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t61 :=
  t60 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t61.


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

Lemma Cons_exists: (forall T: Type, forall self60: List T, ((true = isCons T self60)) <-> ((exists tmp23: List T, exists tmp22: T, (Cons_construct T tmp22 tmp23 = self60)))). 
Proof.
	repeat t61 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self61: List T, ((true = isNil T self61)) <-> (((Nil_construct T = self61)))). 
Proof.
	repeat t61 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic7 := match goal with 
	| [ H30: (true = isCons ?T ?self62) |- _ ] => 
			poseNew (Mark (T,self62) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H30)
	| [ H30: (isCons ?T ?self62 = true) |- _ ] => 
			poseNew (Mark (T,self62) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H30))
	| [ H31: (true = isNil ?T ?self63) |- _ ] => 
			poseNew (Mark (T,self63) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H31)
	| [ H31: (isNil ?T ?self63 = true) |- _ ] => 
			poseNew (Mark (T,self63) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H31))
	| _ => Option_tactic7
end.

Ltac t62 :=
  t_base ||
  List_tactic7 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t63 :=
  t62 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t63.

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
  Start of foldLeft
 ***********************)


Definition foldLeft_rt_type (T: Type) (R: Type) (thiss6: List T) (z: R) (f1: R -> (T -> R)) : Type :=
R.

Fail Next Obligation.

Hint Unfold foldLeft_rt_type.


Equations (noind) foldLeft (T: Type) (R: Type) (thiss6: List T) (z: R) (f1: R -> (T -> R)) : foldLeft_rt_type T R thiss6 z f1 := 
	foldLeft T R thiss6 z f1 by rec ignore_termination lt :=
	foldLeft T R thiss6 z f1 := match thiss6 with
	| Nil_construct _ => z
	| Cons_construct _ h4 t64 => foldLeft T R t64 (f1 z h4) f1
	end.

Hint Unfold foldLeft_comp_proj.

Solve Obligations with (repeat t63).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A5 := match goal with 
	| [ H137: context[foldLeft ?T ?R ?thiss6 ?z ?f1] |- _ ] => 
			poseNew (Mark (T,R,thiss6,z,f1) "unfolding foldLeft_equation")
	| [  |- context[foldLeft ?T ?R ?thiss6 ?z ?f1] ] => 
			poseNew (Mark (T,R,thiss6,z,f1) "unfolding foldLeft_equation")
end.

Ltac rwrtTac_B5 := match goal with 
	| [ H137: context[foldLeft ?T ?R ?thiss6 ?z ?f1], H237: Marked (?T,?R,?thiss6,?z,?f1) "unfolding foldLeft_equation" |- _ ] => 
			poseNew (Mark (T,R,thiss6,z,f1) "unfolded foldLeft_equation");
			add_equation (foldLeft_equation_1 T R thiss6 z f1)
	| [ H237: Marked (?T,?R,?thiss6,?z,?f1) "unfolding foldLeft_equation" |- context[foldLeft ?T ?R ?thiss6 ?z ?f1] ] => 
			poseNew (Mark (T,R,thiss6,z,f1) "unfolded foldLeft_equation");
			add_equation (foldLeft_equation_1 T R thiss6 z f1)
end.

Ltac rwrtTac5 := idtac; repeat rwrtTac_A5; repeat rwrtTac_B5.

Ltac t65 :=
  t_base ||
  List_tactic7 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t66 :=
  t65 ||
  rwrtTac5 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t66.

(***********************
  End of foldLeft
 ***********************)
