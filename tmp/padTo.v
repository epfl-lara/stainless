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

Ltac t520 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t521 :=
  t520 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t521.


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

Lemma None_exists: (forall T: Type, forall self416: Option T, ((true = isNone T self416)) <-> (((None_construct T = self416)))). 
Proof.
	repeat t521 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self417: Option T, ((true = isSome T self417)) <-> ((exists tmp156: T, (Some_construct T tmp156 = self417)))). 
Proof.
	repeat t521 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic52 := match goal with 
	| [ H208: (true = isNone ?T ?self418) |- _ ] => 
			poseNew (Mark (T,self418) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H208)
	| [ H208: (isNone ?T ?self418 = true) |- _ ] => 
			poseNew (Mark (T,self418) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H208))
	| [ H209: (true = isSome ?T ?self419) |- _ ] => 
			poseNew (Mark (T,self419) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H209)
	| [ H209: (isSome ?T ?self419 = true) |- _ ] => 
			poseNew (Mark (T,self419) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H209))
	| _ => idtac
end.

Ltac t522 :=
  t_base ||
  Option_tactic52 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t523 :=
  t522 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t523.


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

Lemma Cons_exists: (forall T: Type, forall self420: List T, ((true = isCons T self420)) <-> ((exists tmp158: List T, exists tmp157: T, (Cons_construct T tmp157 tmp158 = self420)))). 
Proof.
	repeat t523 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self421: List T, ((true = isNil T self421)) <-> (((Nil_construct T = self421)))). 
Proof.
	repeat t523 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic52 := match goal with 
	| [ H210: (true = isCons ?T ?self422) |- _ ] => 
			poseNew (Mark (T,self422) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H210)
	| [ H210: (isCons ?T ?self422 = true) |- _ ] => 
			poseNew (Mark (T,self422) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H210))
	| [ H211: (true = isNil ?T ?self423) |- _ ] => 
			poseNew (Mark (T,self423) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H211)
	| [ H211: (isNil ?T ?self423 = true) |- _ ] => 
			poseNew (Mark (T,self423) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H211))
	| _ => Option_tactic52
end.

Ltac t524 :=
  t_base ||
  List_tactic52 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t525 :=
  t524 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t525.

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
Definition content_rt23_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt23_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt23_type T thiss1 := 
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

Ltac rwrtTac_A92 := match goal with 
	| [ H1304: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B92 := match goal with 
	| [ H1304: context[content ?T ?thiss1], H2304: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2304: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac92 := idtac; repeat rwrtTac_A92; repeat rwrtTac_B92.

Ltac t526 :=
  t_base ||
  List_tactic52 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t527 :=
  t526 ||
  rwrtTac92 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t527.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt21_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt21_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt21_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A93 := match goal with 
	| [ H1305: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B93 := match goal with 
	| [ H1305: context[size ?T ?thiss30], H2305: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2305: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac93 := rwrtTac92; repeat rwrtTac_A93; repeat rwrtTac_B93.

Ltac t528 :=
  t_base ||
  List_tactic52 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t529 :=
  t528 ||
  rwrtTac93 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t529.

(***********************
  End of size
 ***********************)


(***********************
  Start of padTo
 ***********************)


Definition padTo_rt_type (T: Type) (thiss50: List T) (s2: Z) (e2: T) : Type :=
{res15: List T | (ifthenelse (Z.leb s2 (proj1_sig (size T thiss50))) bool
	(fun _ => propInBool ((res15 = thiss50)) )
	(fun _ => ifthenelse (Zeq_bool (proj1_sig (size T res15)) s2) bool
		(fun _ => set_equality (content T res15) (set_union (content T thiss50) (set_union (@set_empty T) (set_singleton e2))) )
		(fun _ => false ) ) = true)}.

Fail Next Obligation.

Hint Unfold padTo_rt_type.


Equations (noind) padTo (T: Type) (thiss50: List T) (s2: Z) (e2: T) : padTo_rt_type T thiss50 s2 e2 := 
	padTo T thiss50 s2 e2 by rec ignore_termination lt :=
	padTo T thiss50 s2 e2 := ifthenelse (Z.leb s2 (0)%Z) (List T)
		(fun _ => thiss50 )
		(fun _ => ifthenelse (isNil _ thiss50) (List T)
			(fun _ => Cons_construct T e2 (proj1_sig (padTo T (Nil_construct T) (Z.sub s2 (1)%Z) e2)) )
			(fun _ => ifthenelse (isCons _ thiss50) (List T)
				(fun _ => Cons_construct T (h T thiss50) (proj1_sig (padTo T (t7 T thiss50) (Z.sub s2 (1)%Z) e2)) )
				(fun _ => let contradiction: False := _ in match contradiction with end ) ) ).

Hint Unfold padTo_comp_proj.

Solve Obligations with (repeat t529).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A94 := match goal with 
	| [ H1306: context[padTo ?T ?thiss50 ?s2 ?e2] |- _ ] => 
			poseNew (Mark (T,thiss50,s2,e2) "unfolding padTo_equation")
	| [  |- context[padTo ?T ?thiss50 ?s2 ?e2] ] => 
			poseNew (Mark (T,thiss50,s2,e2) "unfolding padTo_equation")
end.

Ltac rwrtTac_B94 := match goal with 
	| [ H1306: context[padTo ?T ?thiss50 ?s2 ?e2], H2306: Marked (?T,?thiss50,?s2,?e2) "unfolding padTo_equation" |- _ ] => 
			poseNew (Mark (T,thiss50,s2,e2) "unfolded padTo_equation");
			add_equation (padTo_equation_1 T thiss50 s2 e2)
	| [ H2306: Marked (?T,?thiss50,?s2,?e2) "unfolding padTo_equation" |- context[padTo ?T ?thiss50 ?s2 ?e2] ] => 
			poseNew (Mark (T,thiss50,s2,e2) "unfolded padTo_equation");
			add_equation (padTo_equation_1 T thiss50 s2 e2)
end.

Ltac rwrtTac94 := rwrtTac93; repeat rwrtTac_A94; repeat rwrtTac_B94.

Ltac t530 :=
  t_base ||
  List_tactic52 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t531 :=
  t530 ||
  rwrtTac94 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t531.

(***********************
  End of padTo
 ***********************)
