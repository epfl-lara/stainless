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

Ltac t638 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t639 :=
  t638 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t639.


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

Lemma None_exists: (forall T: Type, forall self488: Option T, ((true = isNone T self488)) <-> (((None_construct T = self488)))). 
Proof.
	repeat t639 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self489: Option T, ((true = isSome T self489)) <-> ((exists tmp183: T, (Some_construct T tmp183 = self489)))). 
Proof.
	repeat t639 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic61 := match goal with 
	| [ H244: (true = isNone ?T ?self490) |- _ ] => 
			poseNew (Mark (T,self490) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H244)
	| [ H244: (isNone ?T ?self490 = true) |- _ ] => 
			poseNew (Mark (T,self490) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H244))
	| [ H245: (true = isSome ?T ?self491) |- _ ] => 
			poseNew (Mark (T,self491) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H245)
	| [ H245: (isSome ?T ?self491 = true) |- _ ] => 
			poseNew (Mark (T,self491) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H245))
	| _ => idtac
end.

Ltac t640 :=
  t_base ||
  Option_tactic61 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t641 :=
  t640 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t641.


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

Lemma Cons_exists: (forall T: Type, forall self492: List T, ((true = isCons T self492)) <-> ((exists tmp185: List T, exists tmp184: T, (Cons_construct T tmp184 tmp185 = self492)))). 
Proof.
	repeat t641 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self493: List T, ((true = isNil T self493)) <-> (((Nil_construct T = self493)))). 
Proof.
	repeat t641 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic61 := match goal with 
	| [ H246: (true = isCons ?T ?self494) |- _ ] => 
			poseNew (Mark (T,self494) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H246)
	| [ H246: (isCons ?T ?self494 = true) |- _ ] => 
			poseNew (Mark (T,self494) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H246))
	| [ H247: (true = isNil ?T ?self495) |- _ ] => 
			poseNew (Mark (T,self495) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H247)
	| [ H247: (isNil ?T ?self495 = true) |- _ ] => 
			poseNew (Mark (T,self495) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H247))
	| _ => Option_tactic61
end.

Ltac t642 :=
  t_base ||
  List_tactic61 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t643 :=
  t642 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t643.

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
Definition content_rt30_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt30_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt30_type T thiss1 := 
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

Ltac rwrtTac_A122 := match goal with 
	| [ H1370: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B122 := match goal with 
	| [ H1370: context[content ?T ?thiss1], H2370: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2370: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac122 := idtac; repeat rwrtTac_A122; repeat rwrtTac_B122.

Ltac t644 :=
  t_base ||
  List_tactic61 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t645 :=
  t644 ||
  rwrtTac122 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t645.

(***********************
  End of content
 ***********************)

(***********************
  Start of contains
 ***********************)

Obligation Tactic:=idtac.
Definition contains_rt5_type (T: Type) (thiss2: List T) (v1: T) : Type :=
{x___2: bool | (Bool.eqb x___2 (set_elem_of v1 (content T thiss2)) = true)}.

Fail Next Obligation.

Hint Unfold contains_rt5_type.


Equations (noind) contains (T: Type) (thiss2: List T) (v1: T) : contains_rt5_type T thiss2 v1 := 
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

Ltac rwrtTac_A123 := match goal with 
	| [ H1371: context[contains ?T ?thiss2 ?v1] |- _ ] => 
			poseNew (Mark (T,thiss2,v1) "unfolding contains_equation")
	| [  |- context[contains ?T ?thiss2 ?v1] ] => 
			poseNew (Mark (T,thiss2,v1) "unfolding contains_equation")
end.

Ltac rwrtTac_B123 := match goal with 
	| [ H1371: context[contains ?T ?thiss2 ?v1], H2371: Marked (?T,?thiss2,?v1) "unfolding contains_equation" |- _ ] => 
			poseNew (Mark (T,thiss2,v1) "unfolded contains_equation");
			add_equation (contains_equation_1 T thiss2 v1)
	| [ H2371: Marked (?T,?thiss2,?v1) "unfolding contains_equation" |- context[contains ?T ?thiss2 ?v1] ] => 
			poseNew (Mark (T,thiss2,v1) "unfolded contains_equation");
			add_equation (contains_equation_1 T thiss2 v1)
end.

Ltac rwrtTac123 := rwrtTac122; repeat rwrtTac_A123; repeat rwrtTac_B123.

Ltac t646 :=
  t_base ||
  List_tactic61 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t647 :=
  t646 ||
  rwrtTac123 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t647.

(***********************
  End of contains
 ***********************)

(***********************
  Start of head
 ***********************)

Definition head (T: Type) (thiss14: List T) (contractHyp187: (negb (propInBool ((thiss14 = Nil_construct T))) = true)) : T :=
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

Definition tail (T: Type) (thiss56: List T) (contractHyp188: (negb (propInBool ((thiss56 = Nil_construct T))) = true)) : List T :=
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

Obligation Tactic:=idtac.
Definition split_rt1_type (T: Type) (thiss58: List T) (seps: List T) : Type :=
{res21: List (List T) | (negb (propInBool ((res21 = Nil_construct (List T)))) = true)}.

Fail Next Obligation.

Hint Unfold split_rt1_type.


Equations (noind) split (T: Type) (thiss58: List T) (seps: List T) : split_rt1_type T thiss58 seps := 
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

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A124 := match goal with 
	| [ H1372: context[split ?T ?thiss58 ?seps] |- _ ] => 
			poseNew (Mark (T,thiss58,seps) "unfolding split_equation")
	| [  |- context[split ?T ?thiss58 ?seps] ] => 
			poseNew (Mark (T,thiss58,seps) "unfolding split_equation")
end.

Ltac rwrtTac_B124 := match goal with 
	| [ H1372: context[split ?T ?thiss58 ?seps], H2372: Marked (?T,?thiss58,?seps) "unfolding split_equation" |- _ ] => 
			poseNew (Mark (T,thiss58,seps) "unfolded split_equation");
			add_equation (split_equation_1 T thiss58 seps)
	| [ H2372: Marked (?T,?thiss58,?seps) "unfolding split_equation" |- context[split ?T ?thiss58 ?seps] ] => 
			poseNew (Mark (T,thiss58,seps) "unfolded split_equation");
			add_equation (split_equation_1 T thiss58 seps)
end.

Ltac rwrtTac124 := rwrtTac123; repeat rwrtTac_A124; repeat rwrtTac_B124.

Ltac t648 :=
  t_base ||
  List_tactic61 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t649 :=
  t648 ||
  rwrtTac124 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t649.

(***********************
  End of split
 ***********************)


(***********************
  Start of splitAt
 ***********************)

Definition splitAt (T: Type) (thiss59: List T) (e3: T) : List (List T) :=
proj1_sig (split T thiss59 (Cons_construct T e3 (Nil_construct T))).

Fail Next Obligation.

Hint Unfold splitAt: definitions.

(***********************
  End of splitAt
 ***********************)
