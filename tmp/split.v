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

Ltac t625 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t626 :=
  t625 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t626.


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

Lemma None_exists: (forall T: Type, forall self480: Option T, ((true = isNone T self480)) <-> (((None_construct T = self480)))). 
Proof.
	repeat t626 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self481: Option T, ((true = isSome T self481)) <-> ((exists tmp180: T, (Some_construct T tmp180 = self481)))). 
Proof.
	repeat t626 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic60 := match goal with 
	| [ H240: (true = isNone ?T ?self482) |- _ ] => 
			poseNew (Mark (T,self482) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H240)
	| [ H240: (isNone ?T ?self482 = true) |- _ ] => 
			poseNew (Mark (T,self482) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H240))
	| [ H241: (true = isSome ?T ?self483) |- _ ] => 
			poseNew (Mark (T,self483) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H241)
	| [ H241: (isSome ?T ?self483 = true) |- _ ] => 
			poseNew (Mark (T,self483) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H241))
	| _ => idtac
end.

Ltac t627 :=
  t_base ||
  Option_tactic60 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t628 :=
  t627 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t628.


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

Lemma Cons_exists: (forall T: Type, forall self484: List T, ((true = isCons T self484)) <-> ((exists tmp182: List T, exists tmp181: T, (Cons_construct T tmp181 tmp182 = self484)))). 
Proof.
	repeat t628 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self485: List T, ((true = isNil T self485)) <-> (((Nil_construct T = self485)))). 
Proof.
	repeat t628 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic60 := match goal with 
	| [ H242: (true = isCons ?T ?self486) |- _ ] => 
			poseNew (Mark (T,self486) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H242)
	| [ H242: (isCons ?T ?self486 = true) |- _ ] => 
			poseNew (Mark (T,self486) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H242))
	| [ H243: (true = isNil ?T ?self487) |- _ ] => 
			poseNew (Mark (T,self487) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H243)
	| [ H243: (isNil ?T ?self487 = true) |- _ ] => 
			poseNew (Mark (T,self487) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H243))
	| _ => Option_tactic60
end.

Ltac t629 :=
  t_base ||
  List_tactic60 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t630 :=
  t629 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t630.

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
Definition content_rt29_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt29_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt29_type T thiss1 := 
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

Ltac rwrtTac_A119 := match goal with 
	| [ H1363: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B119 := match goal with 
	| [ H1363: context[content ?T ?thiss1], H2363: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2363: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac119 := idtac; repeat rwrtTac_A119; repeat rwrtTac_B119.

Ltac t631 :=
  t_base ||
  List_tactic60 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t632 :=
  t631 ||
  rwrtTac119 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t632.

(***********************
  End of content
 ***********************)

(***********************
  Start of contains
 ***********************)

Obligation Tactic:=idtac.
Definition contains_rt4_type (T: Type) (thiss2: List T) (v1: T) : Type :=
{x___2: bool | (Bool.eqb x___2 (set_elem_of v1 (content T thiss2)) = true)}.

Fail Next Obligation.

Hint Unfold contains_rt4_type.


Equations (noind) contains (T: Type) (thiss2: List T) (v1: T) : contains_rt4_type T thiss2 v1 := 
	contains T thiss2 v1 by rec ignore_termination lt :=
	contains T thiss2 v1 := match thiss2 with
	| Cons_construct _ h2 t26 => 
			ifthenelse (propInBool ((h2 = v1))) bool
				(fun _ => true )
				(fun _ => proj1_sig (contains T t26 v1) )
	| Nil_construct _ => false
	end.

Hint Unfold contains_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A120 := match goal with 
	| [ H1364: context[contains ?T ?thiss2 ?v1] |- _ ] => 
			poseNew (Mark (T,thiss2,v1) "unfolding contains_equation")
	| [  |- context[contains ?T ?thiss2 ?v1] ] => 
			poseNew (Mark (T,thiss2,v1) "unfolding contains_equation")
end.

Ltac rwrtTac_B120 := match goal with 
	| [ H1364: context[contains ?T ?thiss2 ?v1], H2364: Marked (?T,?thiss2,?v1) "unfolding contains_equation" |- _ ] => 
			poseNew (Mark (T,thiss2,v1) "unfolded contains_equation");
			add_equation (contains_equation_1 T thiss2 v1)
	| [ H2364: Marked (?T,?thiss2,?v1) "unfolding contains_equation" |- context[contains ?T ?thiss2 ?v1] ] => 
			poseNew (Mark (T,thiss2,v1) "unfolded contains_equation");
			add_equation (contains_equation_1 T thiss2 v1)
end.

Ltac rwrtTac120 := rwrtTac119; repeat rwrtTac_A120; repeat rwrtTac_B120.

Ltac t633 :=
  t_base ||
  List_tactic60 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t634 :=
  t633 ||
  rwrtTac120 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t634.

(***********************
  End of contains
 ***********************)

(***********************
  Start of head
 ***********************)

Definition head (T: Type) (thiss14: List T) (contractHyp182: (negb (propInBool ((thiss14 = Nil_construct T))) = true)) : T :=
ifthenelse (isCons _ thiss14) T
	(fun _ => h T thiss14 )
	(fun _ => let contradiction: False := _ in match contradiction with end ).

Fail Next Obligation.

Hint Unfold head: definitions.

(***********************
  End of head
 ***********************)

(***********************
  Start of tail
 ***********************)

Definition tail (T: Type) (thiss56: List T) (contractHyp183: (negb (propInBool ((thiss56 = Nil_construct T))) = true)) : List T :=
ifthenelse (isCons _ thiss56) (List T)
	(fun _ => t7 T thiss56 )
	(fun _ => let contradiction: False := _ in match contradiction with end ).

Fail Next Obligation.

Hint Unfold tail: definitions.

(***********************
  End of tail
 ***********************)


(***********************
  Start of split
 ***********************)


Definition split_rt_type (T: Type) (thiss58: List T) (seps: List T) : Type :=
{res21: List (List T) | (negb (propInBool ((res21 = Nil_construct (List T)))) = true)}.

Fail Next Obligation.

Hint Unfold split_rt_type.


Equations (noind) split (T: Type) (thiss58: List T) (seps: List T) : split_rt_type T thiss58 seps := 
	split T thiss58 seps by rec ignore_termination lt :=
	split T thiss58 seps := match thiss58 with
	| Cons_construct _ h24 t635 => 
			ifthenelse (proj1_sig (contains T seps h24)) (List (List T))
				(fun _ => Cons_construct (List T) (Nil_construct T) (proj1_sig (split T t635 seps)) )
				(fun _ => let r3 := (proj1_sig (split T t635 seps)) in (Cons_construct (List T) (Cons_construct T h24 (head (List T) r3 _)) (tail (List T) r3 _)) )
	| Nil_construct _ => 
			Cons_construct (List T) (Nil_construct T) (Nil_construct (List T))
	end.

Hint Unfold split_comp_proj.

Solve Obligations with (repeat t634).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A121 := match goal with 
	| [ H1365: context[split ?T ?thiss58 ?seps] |- _ ] => 
			poseNew (Mark (T,thiss58,seps) "unfolding split_equation")
	| [  |- context[split ?T ?thiss58 ?seps] ] => 
			poseNew (Mark (T,thiss58,seps) "unfolding split_equation")
end.

Ltac rwrtTac_B121 := match goal with 
	| [ H1365: context[split ?T ?thiss58 ?seps], H2365: Marked (?T,?thiss58,?seps) "unfolding split_equation" |- _ ] => 
			poseNew (Mark (T,thiss58,seps) "unfolded split_equation");
			add_equation (split_equation_1 T thiss58 seps)
	| [ H2365: Marked (?T,?thiss58,?seps) "unfolding split_equation" |- context[split ?T ?thiss58 ?seps] ] => 
			poseNew (Mark (T,thiss58,seps) "unfolded split_equation");
			add_equation (split_equation_1 T thiss58 seps)
end.

Ltac rwrtTac121 := rwrtTac120; repeat rwrtTac_A121; repeat rwrtTac_B121.

Ltac t636 :=
  t_base ||
  List_tactic60 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t637 :=
  t636 ||
  rwrtTac121 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t637.

(***********************
  End of split
 ***********************)
