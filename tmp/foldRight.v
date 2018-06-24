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

Ltac t67 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t68 :=
  t67 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t68.


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

Lemma None_exists: (forall T: Type, forall self64: Option T, ((true = isNone T self64)) <-> (((None_construct T = self64)))). 
Proof.
	repeat t68 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self65: Option T, ((true = isSome T self65)) <-> ((exists tmp24: T, (Some_construct T tmp24 = self65)))). 
Proof.
	repeat t68 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic8 := match goal with 
	| [ H32: (true = isNone ?T ?self66) |- _ ] => 
			poseNew (Mark (T,self66) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H32)
	| [ H32: (isNone ?T ?self66 = true) |- _ ] => 
			poseNew (Mark (T,self66) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H32))
	| [ H33: (true = isSome ?T ?self67) |- _ ] => 
			poseNew (Mark (T,self67) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H33)
	| [ H33: (isSome ?T ?self67 = true) |- _ ] => 
			poseNew (Mark (T,self67) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H33))
	| _ => idtac
end.

Ltac t69 :=
  t_base ||
  Option_tactic8 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t70 :=
  t69 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t70.


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

Lemma Cons_exists: (forall T: Type, forall self68: List T, ((true = isCons T self68)) <-> ((exists tmp26: List T, exists tmp25: T, (Cons_construct T tmp25 tmp26 = self68)))). 
Proof.
	repeat t70 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self69: List T, ((true = isNil T self69)) <-> (((Nil_construct T = self69)))). 
Proof.
	repeat t70 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic8 := match goal with 
	| [ H34: (true = isCons ?T ?self70) |- _ ] => 
			poseNew (Mark (T,self70) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H34)
	| [ H34: (isCons ?T ?self70 = true) |- _ ] => 
			poseNew (Mark (T,self70) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H34))
	| [ H35: (true = isNil ?T ?self71) |- _ ] => 
			poseNew (Mark (T,self71) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H35)
	| [ H35: (isNil ?T ?self71 = true) |- _ ] => 
			poseNew (Mark (T,self71) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H35))
	| _ => Option_tactic8
end.

Ltac t71 :=
  t_base ||
  List_tactic8 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t72 :=
  t71 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t72.

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
  Start of foldRight
 ***********************)


Definition foldRight_rt_type (T: Type) (R: Type) (thiss7: List T) (z1: R) (f2: T -> (R -> R)) : Type :=
R.

Fail Next Obligation.

Hint Unfold foldRight_rt_type.


Equations (noind) foldRight (T: Type) (R: Type) (thiss7: List T) (z1: R) (f2: T -> (R -> R)) : foldRight_rt_type T R thiss7 z1 f2 := 
	foldRight T R thiss7 z1 f2 by rec ignore_termination lt :=
	foldRight T R thiss7 z1 f2 := match thiss7 with
	| Nil_construct _ => z1
	| Cons_construct _ h5 t73 => f2 h5 (foldRight T R t73 z1 f2)
	end.

Hint Unfold foldRight_comp_proj.

Solve Obligations with (repeat t72).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A6 := match goal with 
	| [ H142: context[foldRight ?T ?R ?thiss7 ?z1 ?f2] |- _ ] => 
			poseNew (Mark (T,R,thiss7,z1,f2) "unfolding foldRight_equation")
	| [  |- context[foldRight ?T ?R ?thiss7 ?z1 ?f2] ] => 
			poseNew (Mark (T,R,thiss7,z1,f2) "unfolding foldRight_equation")
end.

Ltac rwrtTac_B6 := match goal with 
	| [ H142: context[foldRight ?T ?R ?thiss7 ?z1 ?f2], H242: Marked (?T,?R,?thiss7,?z1,?f2) "unfolding foldRight_equation" |- _ ] => 
			poseNew (Mark (T,R,thiss7,z1,f2) "unfolded foldRight_equation");
			add_equation (foldRight_equation_1 T R thiss7 z1 f2)
	| [ H242: Marked (?T,?R,?thiss7,?z1,?f2) "unfolding foldRight_equation" |- context[foldRight ?T ?R ?thiss7 ?z1 ?f2] ] => 
			poseNew (Mark (T,R,thiss7,z1,f2) "unfolded foldRight_equation");
			add_equation (foldRight_equation_1 T R thiss7 z1 f2)
end.

Ltac rwrtTac6 := idtac; repeat rwrtTac_A6; repeat rwrtTac_B6.

Ltac t74 :=
  t_base ||
  List_tactic8 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t75 :=
  t74 ||
  rwrtTac6 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t75.

(***********************
  End of foldRight
 ***********************)
