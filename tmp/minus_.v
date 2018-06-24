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

Ltac t276 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t277 :=
  t276 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t277.


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

Lemma None_exists: (forall T: Type, forall self272: Option T, ((true = isNone T self272)) <-> (((None_construct T = self272)))). 
Proof.
	repeat t277 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self273: Option T, ((true = isSome T self273)) <-> ((exists tmp102: T, (Some_construct T tmp102 = self273)))). 
Proof.
	repeat t277 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic34 := match goal with 
	| [ H136: (true = isNone ?T ?self274) |- _ ] => 
			poseNew (Mark (T,self274) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H136)
	| [ H136: (isNone ?T ?self274 = true) |- _ ] => 
			poseNew (Mark (T,self274) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H136))
	| [ H137: (true = isSome ?T ?self275) |- _ ] => 
			poseNew (Mark (T,self275) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H137)
	| [ H137: (isSome ?T ?self275 = true) |- _ ] => 
			poseNew (Mark (T,self275) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H137))
	| _ => idtac
end.

Ltac t278 :=
  t_base ||
  Option_tactic34 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t279 :=
  t278 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t279.


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

Lemma Cons_exists: (forall T: Type, forall self276: List T, ((true = isCons T self276)) <-> ((exists tmp104: List T, exists tmp103: T, (Cons_construct T tmp103 tmp104 = self276)))). 
Proof.
	repeat t279 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self277: List T, ((true = isNil T self277)) <-> (((Nil_construct T = self277)))). 
Proof.
	repeat t279 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic34 := match goal with 
	| [ H138: (true = isCons ?T ?self278) |- _ ] => 
			poseNew (Mark (T,self278) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H138)
	| [ H138: (isCons ?T ?self278 = true) |- _ ] => 
			poseNew (Mark (T,self278) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H138))
	| [ H139: (true = isNil ?T ?self279) |- _ ] => 
			poseNew (Mark (T,self279) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H139)
	| [ H139: (isNil ?T ?self279 = true) |- _ ] => 
			poseNew (Mark (T,self279) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H139))
	| _ => Option_tactic34
end.

Ltac t280 :=
  t_base ||
  List_tactic34 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t281 :=
  t280 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t281.

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
Definition content_rt7_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt7_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt7_type T thiss1 := 
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

Ltac rwrtTac_A28 := match goal with 
	| [ H1168: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B28 := match goal with 
	| [ H1168: context[content ?T ?thiss1], H2168: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2168: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac28 := idtac; repeat rwrtTac_A28; repeat rwrtTac_B28.

Ltac t282 :=
  t_base ||
  List_tactic34 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t283 :=
  t282 ||
  rwrtTac28 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t283.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt3_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt3_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt3_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A29 := match goal with 
	| [ H1169: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B29 := match goal with 
	| [ H1169: context[size ?T ?thiss30], H2169: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2169: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac29 := rwrtTac28; repeat rwrtTac_A29; repeat rwrtTac_B29.

Ltac t284 :=
  t_base ||
  List_tactic34 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t285 :=
  t284 ||
  rwrtTac29 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t285.

(***********************
  End of size
 ***********************)


(***********************
  Start of -
 ***********************)


Definition minus__rt_type (T: Type) (thiss33: List T) (e: T) : Type :=
{res4: List T | (ifthenelse (Z.leb (proj1_sig (size T res4)) (proj1_sig (size T thiss33))) bool
	(fun _ => set_equality (content T res4) (set_difference (content T thiss33) (set_union (@set_empty T) (set_singleton e))) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold minus__rt_type.


Equations (noind) minus_ (T: Type) (thiss33: List T) (e: T) : minus__rt_type T thiss33 e := 
	minus_ T thiss33 e by rec ignore_termination lt :=
	minus_ T thiss33 e := match thiss33 with
	| Cons_construct _ h14 t286 => 
			ifthenelse (propInBool ((e = h14))) (List T)
				(fun _ => proj1_sig (minus_ T t286 e) )
				(fun _ => Cons_construct T h14 (proj1_sig (minus_ T t286 e)) )
	| Nil_construct _ => Nil_construct T
	end.

Hint Unfold minus__comp_proj.

Solve Obligations with (repeat t285).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A30 := match goal with 
	| [ H1170: context[minus_ ?T ?thiss33 ?e] |- _ ] => 
			poseNew (Mark (T,thiss33,e) "unfolding minus__equation")
	| [  |- context[minus_ ?T ?thiss33 ?e] ] => 
			poseNew (Mark (T,thiss33,e) "unfolding minus__equation")
end.

Ltac rwrtTac_B30 := match goal with 
	| [ H1170: context[minus_ ?T ?thiss33 ?e], H2170: Marked (?T,?thiss33,?e) "unfolding minus__equation" |- _ ] => 
			poseNew (Mark (T,thiss33,e) "unfolded minus__equation");
			add_equation (minus__equation_1 T thiss33 e)
	| [ H2170: Marked (?T,?thiss33,?e) "unfolding minus__equation" |- context[minus_ ?T ?thiss33 ?e] ] => 
			poseNew (Mark (T,thiss33,e) "unfolded minus__equation");
			add_equation (minus__equation_1 T thiss33 e)
end.

Ltac rwrtTac30 := rwrtTac29; repeat rwrtTac_A30; repeat rwrtTac_B30.

Ltac t287 :=
  t_base ||
  List_tactic34 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t288 :=
  t287 ||
  rwrtTac30 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t288.

(***********************
  End of -
 ***********************)
