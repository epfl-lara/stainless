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

Ltac t9 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t10 :=
  t9 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t10.


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

Lemma None_exists: (forall T: Type, forall self8: Option T, ((true = isNone T self8)) <-> (((None_construct T = self8)))). 
Proof.
	repeat t10 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self9: Option T, ((true = isSome T self9)) <-> ((exists tmp3: T, (Some_construct T tmp3 = self9)))). 
Proof.
	repeat t10 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic1 := match goal with 
	| [ H4: (true = isNone ?T ?self10) |- _ ] => 
			poseNew (Mark (T,self10) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H4)
	| [ H4: (isNone ?T ?self10 = true) |- _ ] => 
			poseNew (Mark (T,self10) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H4))
	| [ H5: (true = isSome ?T ?self11) |- _ ] => 
			poseNew (Mark (T,self11) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H5)
	| [ H5: (isSome ?T ?self11 = true) |- _ ] => 
			poseNew (Mark (T,self11) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H5))
	| _ => idtac
end.

Ltac t11 :=
  t_base ||
  Option_tactic1 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t12 :=
  t11 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t12.


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

Lemma Cons_exists: (forall T: Type, forall self12: List T, ((true = isCons T self12)) <-> ((exists tmp5: List T, exists tmp4: T, (Cons_construct T tmp4 tmp5 = self12)))). 
Proof.
	repeat t12 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self13: List T, ((true = isNil T self13)) <-> (((Nil_construct T = self13)))). 
Proof.
	repeat t12 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic1 := match goal with 
	| [ H6: (true = isCons ?T ?self14) |- _ ] => 
			poseNew (Mark (T,self14) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H6)
	| [ H6: (isCons ?T ?self14 = true) |- _ ] => 
			poseNew (Mark (T,self14) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H6))
	| [ H7: (true = isNil ?T ?self15) |- _ ] => 
			poseNew (Mark (T,self15) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H7)
	| [ H7: (isNil ?T ?self15 = true) |- _ ] => 
			poseNew (Mark (T,self15) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H7))
	| _ => Option_tactic1
end.

Ltac t13 :=
  t_base ||
  List_tactic1 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t14 :=
  t13 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t14.

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
  Start of content
 ***********************)


Definition content_rt_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt_type T thiss1 := 
	content T thiss1 by rec ignore_termination lt :=
	content T thiss1 := match thiss1 with
	| Nil_construct _ => @set_empty T
	| Cons_construct _ h1 t15 => 
			set_union (set_union (@set_empty T) (set_singleton h1)) (content T t15)
	end.

Hint Unfold content_comp_proj.

Solve Obligations with (repeat t14).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A := match goal with 
	| [ H18: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B := match goal with 
	| [ H18: context[content ?T ?thiss1], H28: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H28: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac := idtac; repeat rwrtTac_A; repeat rwrtTac_B.

Ltac t16 :=
  t_base ||
  List_tactic1 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t17 :=
  t16 ||
  rwrtTac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t17.

(***********************
  End of content
 ***********************)
