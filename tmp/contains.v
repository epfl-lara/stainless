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

Ltac t18 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t19 :=
  t18 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t19.


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

Lemma None_exists: (forall T: Type, forall self16: Option T, ((true = isNone T self16)) <-> (((None_construct T = self16)))). 
Proof.
	repeat t19 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self17: Option T, ((true = isSome T self17)) <-> ((exists tmp6: T, (Some_construct T tmp6 = self17)))). 
Proof.
	repeat t19 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic2 := match goal with 
	| [ H8: (true = isNone ?T ?self18) |- _ ] => 
			poseNew (Mark (T,self18) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H8)
	| [ H8: (isNone ?T ?self18 = true) |- _ ] => 
			poseNew (Mark (T,self18) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H8))
	| [ H9: (true = isSome ?T ?self19) |- _ ] => 
			poseNew (Mark (T,self19) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H9)
	| [ H9: (isSome ?T ?self19 = true) |- _ ] => 
			poseNew (Mark (T,self19) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H9))
	| _ => idtac
end.

Ltac t20 :=
  t_base ||
  Option_tactic2 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t21 :=
  t20 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t21.


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

Lemma Cons_exists: (forall T: Type, forall self20: List T, ((true = isCons T self20)) <-> ((exists tmp8: List T, exists tmp7: T, (Cons_construct T tmp7 tmp8 = self20)))). 
Proof.
	repeat t21 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self21: List T, ((true = isNil T self21)) <-> (((Nil_construct T = self21)))). 
Proof.
	repeat t21 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic2 := match goal with 
	| [ H10: (true = isCons ?T ?self22) |- _ ] => 
			poseNew (Mark (T,self22) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H10)
	| [ H10: (isCons ?T ?self22 = true) |- _ ] => 
			poseNew (Mark (T,self22) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H10))
	| [ H11: (true = isNil ?T ?self23) |- _ ] => 
			poseNew (Mark (T,self23) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H11)
	| [ H11: (isNil ?T ?self23 = true) |- _ ] => 
			poseNew (Mark (T,self23) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H11))
	| _ => Option_tactic2
end.

Ltac t22 :=
  t_base ||
  List_tactic2 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t23 :=
  t22 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t23.

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

Obligation Tactic:=idtac.
Definition content_rt1_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt1_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt1_type T thiss1 := 
	content T thiss1 by rec ignore_termination lt :=
	content T thiss1 := match thiss1 with
	| Nil_construct _ => @set_empty T
	| Cons_construct _ h1 t15 => 
			set_union (set_union (@set_empty T) (set_singleton h1)) (content T t15)
	end.

Hint Unfold content_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A1 := match goal with 
	| [ H113: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B1 := match goal with 
	| [ H113: context[content ?T ?thiss1], H213: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H213: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac1 := idtac; repeat rwrtTac_A1; repeat rwrtTac_B1.

Ltac t24 :=
  t_base ||
  List_tactic2 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t25 :=
  t24 ||
  rwrtTac1 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t25.

(***********************
  End of content
 ***********************)


(***********************
  Start of contains
 ***********************)


Definition contains_rt_type (T: Type) (thiss2: List T) (v1: T) : Type :=
{x___2: bool | (Bool.eqb x___2 (set_elem_of v1 (content T thiss2)) = true)}.

Fail Next Obligation.

Hint Unfold contains_rt_type.


Equations (noind) contains (T: Type) (thiss2: List T) (v1: T) : contains_rt_type T thiss2 v1 := 
	contains T thiss2 v1 by rec ignore_termination lt :=
	contains T thiss2 v1 := match thiss2 with
	| Cons_construct _ h2 t26 => 
			ifthenelse (propInBool ((h2 = v1))) bool
				(fun _ => true )
				(fun _ => proj1_sig (contains T t26 v1) )
	| Nil_construct _ => false
	end.

Hint Unfold contains_comp_proj.

Solve Obligations with (repeat t25).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A2 := match goal with 
	| [ H114: context[contains ?T ?thiss2 ?v1] |- _ ] => 
			poseNew (Mark (T,thiss2,v1) "unfolding contains_equation")
	| [  |- context[contains ?T ?thiss2 ?v1] ] => 
			poseNew (Mark (T,thiss2,v1) "unfolding contains_equation")
end.

Ltac rwrtTac_B2 := match goal with 
	| [ H114: context[contains ?T ?thiss2 ?v1], H214: Marked (?T,?thiss2,?v1) "unfolding contains_equation" |- _ ] => 
			poseNew (Mark (T,thiss2,v1) "unfolded contains_equation");
			add_equation (contains_equation_1 T thiss2 v1)
	| [ H214: Marked (?T,?thiss2,?v1) "unfolding contains_equation" |- context[contains ?T ?thiss2 ?v1] ] => 
			poseNew (Mark (T,thiss2,v1) "unfolded contains_equation");
			add_equation (contains_equation_1 T thiss2 v1)
end.

Ltac rwrtTac2 := rwrtTac1; repeat rwrtTac_A2; repeat rwrtTac_B2.

Ltac t27 :=
  t_base ||
  List_tactic2 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t28 :=
  t27 ||
  rwrtTac2 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t28.

(***********************
  End of contains
 ***********************)
