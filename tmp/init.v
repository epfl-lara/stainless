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

Ltac t430 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t431 :=
  t430 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t431.


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

Lemma None_exists: (forall T: Type, forall self360: Option T, ((true = isNone T self360)) <-> (((None_construct T = self360)))). 
Proof.
	repeat t431 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self361: Option T, ((true = isSome T self361)) <-> ((exists tmp135: T, (Some_construct T tmp135 = self361)))). 
Proof.
	repeat t431 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic45 := match goal with 
	| [ H180: (true = isNone ?T ?self362) |- _ ] => 
			poseNew (Mark (T,self362) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H180)
	| [ H180: (isNone ?T ?self362 = true) |- _ ] => 
			poseNew (Mark (T,self362) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H180))
	| [ H181: (true = isSome ?T ?self363) |- _ ] => 
			poseNew (Mark (T,self363) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H181)
	| [ H181: (isSome ?T ?self363 = true) |- _ ] => 
			poseNew (Mark (T,self363) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H181))
	| _ => idtac
end.

Ltac t432 :=
  t_base ||
  Option_tactic45 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t433 :=
  t432 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t433.


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

Lemma Cons_exists: (forall T: Type, forall self364: List T, ((true = isCons T self364)) <-> ((exists tmp137: List T, exists tmp136: T, (Cons_construct T tmp136 tmp137 = self364)))). 
Proof.
	repeat t433 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self365: List T, ((true = isNil T self365)) <-> (((Nil_construct T = self365)))). 
Proof.
	repeat t433 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic45 := match goal with 
	| [ H182: (true = isCons ?T ?self366) |- _ ] => 
			poseNew (Mark (T,self366) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H182)
	| [ H182: (isCons ?T ?self366 = true) |- _ ] => 
			poseNew (Mark (T,self366) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H182))
	| [ H183: (true = isNil ?T ?self367) |- _ ] => 
			poseNew (Mark (T,self367) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H183)
	| [ H183: (isNil ?T ?self367 = true) |- _ ] => 
			poseNew (Mark (T,self367) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H183))
	| _ => Option_tactic45
end.

Ltac t434 :=
  t_base ||
  List_tactic45 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t435 :=
  t434 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t435.

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
Definition content_rt18_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt18_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt18_type T thiss1 := 
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

Ltac rwrtTac_A69 := match goal with 
	| [ H1253: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B69 := match goal with 
	| [ H1253: context[content ?T ?thiss1], H2253: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2253: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac69 := idtac; repeat rwrtTac_A69; repeat rwrtTac_B69.

Ltac t436 :=
  t_base ||
  List_tactic45 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t437 :=
  t436 ||
  rwrtTac69 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t437.

(***********************
  End of content
 ***********************)

(***********************
  Start of isEmpty
 ***********************)

Definition isEmpty (T: Type) (thiss17: List T) : bool :=
ifthenelse (isNil _ thiss17) bool
	(fun _ => true )
	(fun _ => false ).

Fail Next Obligation.

Hint Unfold isEmpty: definitions.

(***********************
  End of isEmpty
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt14_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt14_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt14_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A70 := match goal with 
	| [ H1254: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B70 := match goal with 
	| [ H1254: context[size ?T ?thiss30], H2254: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2254: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac70 := rwrtTac69; repeat rwrtTac_A70; repeat rwrtTac_B70.

Ltac t438 :=
  t_base ||
  List_tactic45 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t439 :=
  t438 ||
  rwrtTac70 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t439.

(***********************
  End of size
 ***********************)


(***********************
  Start of init
 ***********************)


Definition contractHyp119_type (T: Type) (thiss43: List T) : Type :=
(negb (isEmpty T thiss43) = true).

Fail Next Obligation.

Hint Unfold contractHyp119_type.


Definition init_rt_type (T: Type) (thiss43: List T) (contractHyp119: contractHyp119_type T thiss43) : Type :=
{r1: List T | (ifthenelse (Zeq_bool (proj1_sig (size T r1)) (Z.sub (proj1_sig (size T thiss43)) (1)%Z)) bool
	(fun _ => set_subset (content T r1) (content T thiss43) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold init_rt_type.


Equations (noind) init (T: Type) (thiss43: List T) (contractHyp119: contractHyp119_type T thiss43) : init_rt_type T thiss43 contractHyp119 := 
	init T thiss43 contractHyp119 by rec ignore_termination lt :=
	init T thiss43 contractHyp119 := ifthenelse
		(ifthenelse (isCons _ thiss43) bool
			(fun _ => isNil _ (t7 T thiss43) )
			(fun _ => false ))
		(List T)
		(fun _ => Nil_construct T )
		(fun _ => ifthenelse (isCons _ thiss43) (List T)
			(fun _ => Cons_construct T (h T thiss43) (proj1_sig (init T (t7 T thiss43) _)) )
			(fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold init_comp_proj.

Solve Obligations with (repeat t439).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A71 := match goal with 
	| [ H1255: context[init ?T ?thiss43] |- _ ] => 
			poseNew (Mark (T,thiss43) "unfolding init_equation")
	| [  |- context[init ?T ?thiss43] ] => 
			poseNew (Mark (T,thiss43) "unfolding init_equation")
end.

Ltac rwrtTac_B71 := match goal with 
	| [ H1255: context[init ?T ?thiss43], H2255: Marked (?T,?thiss43) "unfolding init_equation" |- _ ] => 
			poseNew (Mark (T,thiss43) "unfolded init_equation");
			add_equation (init_equation_1 T thiss43)
	| [ H2255: Marked (?T,?thiss43) "unfolding init_equation" |- context[init ?T ?thiss43] ] => 
			poseNew (Mark (T,thiss43) "unfolded init_equation");
			add_equation (init_equation_1 T thiss43)
end.

Ltac rwrtTac71 := rwrtTac70; repeat rwrtTac_A71; repeat rwrtTac_B71.

Ltac t440 :=
  t_base ||
  List_tactic45 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t441 :=
  t440 ||
  rwrtTac71 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t441.

(***********************
  End of init
 ***********************)
