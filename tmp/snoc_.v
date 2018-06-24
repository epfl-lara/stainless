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

Ltac t304 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t305 :=
  t304 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t305.


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

Lemma None_exists: (forall T: Type, forall self288: Option T, ((true = isNone T self288)) <-> (((None_construct T = self288)))). 
Proof.
	repeat t305 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self289: Option T, ((true = isSome T self289)) <-> ((exists tmp108: T, (Some_construct T tmp108 = self289)))). 
Proof.
	repeat t305 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic36 := match goal with 
	| [ H144: (true = isNone ?T ?self290) |- _ ] => 
			poseNew (Mark (T,self290) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H144)
	| [ H144: (isNone ?T ?self290 = true) |- _ ] => 
			poseNew (Mark (T,self290) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H144))
	| [ H145: (true = isSome ?T ?self291) |- _ ] => 
			poseNew (Mark (T,self291) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H145)
	| [ H145: (isSome ?T ?self291 = true) |- _ ] => 
			poseNew (Mark (T,self291) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H145))
	| _ => idtac
end.

Ltac t306 :=
  t_base ||
  Option_tactic36 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t307 :=
  t306 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t307.


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

Lemma Cons_exists: (forall T: Type, forall self292: List T, ((true = isCons T self292)) <-> ((exists tmp110: List T, exists tmp109: T, (Cons_construct T tmp109 tmp110 = self292)))). 
Proof.
	repeat t307 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self293: List T, ((true = isNil T self293)) <-> (((Nil_construct T = self293)))). 
Proof.
	repeat t307 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic36 := match goal with 
	| [ H146: (true = isCons ?T ?self294) |- _ ] => 
			poseNew (Mark (T,self294) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H146)
	| [ H146: (isCons ?T ?self294 = true) |- _ ] => 
			poseNew (Mark (T,self294) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H146))
	| [ H147: (true = isNil ?T ?self295) |- _ ] => 
			poseNew (Mark (T,self295) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H147)
	| [ H147: (isNil ?T ?self295 = true) |- _ ] => 
			poseNew (Mark (T,self295) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H147))
	| _ => Option_tactic36
end.

Ltac t308 :=
  t_base ||
  List_tactic36 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t309 :=
  t308 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t309.

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
Definition content_rt9_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt9_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt9_type T thiss1 := 
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

Ltac rwrtTac_A35 := match goal with 
	| [ H1183: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B35 := match goal with 
	| [ H1183: context[content ?T ?thiss1], H2183: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2183: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac35 := idtac; repeat rwrtTac_A35; repeat rwrtTac_B35.

Ltac t310 :=
  t_base ||
  List_tactic36 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t311 :=
  t310 ||
  rwrtTac35 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t311.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt5_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt5_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt5_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A36 := match goal with 
	| [ H1184: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B36 := match goal with 
	| [ H1184: context[size ?T ?thiss30], H2184: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2184: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac36 := rwrtTac35; repeat rwrtTac_A36; repeat rwrtTac_B36.

Ltac t312 :=
  t_base ||
  List_tactic36 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t313 :=
  t312 ||
  rwrtTac36 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t313.

(***********************
  End of size
 ***********************)


(***********************
  Start of :+
 ***********************)


Definition snoc__rt_type (T: Type) (thiss35: List T) (t314: T) : Type :=
{res6: List T | (let assumption := (magic ((isCons _ res6 = true))) in (ifthenelse (Zeq_bool (proj1_sig (size T res6)) (Z.add (proj1_sig (size T thiss35)) (1)%Z)) bool
	(fun _ => set_equality (content T res6) (set_union (content T thiss35) (set_union (@set_empty T) (set_singleton t314))) )
	(fun _ => false )) = true)}.

Fail Next Obligation.

Hint Unfold snoc__rt_type.


Equations (noind) snoc_ (T: Type) (thiss35: List T) (t314: T) : snoc__rt_type T thiss35 t314 := 
	snoc_ T thiss35 t314 by rec ignore_termination lt :=
	snoc_ T thiss35 t314 := match thiss35 with
	| Nil_construct _ => Cons_construct T t314 thiss35
	| Cons_construct _ x3 xs1 => Cons_construct T x3 (proj1_sig (snoc_ T xs1 t314))
	end.

Hint Unfold snoc__comp_proj.

Solve Obligations with (repeat t313).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A37 := match goal with 
	| [ H1185: context[snoc_ ?T ?thiss35 ?t314] |- _ ] => 
			poseNew (Mark (T,thiss35,t314) "unfolding snoc__equation")
	| [  |- context[snoc_ ?T ?thiss35 ?t314] ] => 
			poseNew (Mark (T,thiss35,t314) "unfolding snoc__equation")
end.

Ltac rwrtTac_B37 := match goal with 
	| [ H1185: context[snoc_ ?T ?thiss35 ?t314], H2185: Marked (?T,?thiss35,?t314) "unfolding snoc__equation" |- _ ] => 
			poseNew (Mark (T,thiss35,t314) "unfolded snoc__equation");
			add_equation (snoc__equation_1 T thiss35 t314)
	| [ H2185: Marked (?T,?thiss35,?t314) "unfolding snoc__equation" |- context[snoc_ ?T ?thiss35 ?t314] ] => 
			poseNew (Mark (T,thiss35,t314) "unfolded snoc__equation");
			add_equation (snoc__equation_1 T thiss35 t314)
end.

Ltac rwrtTac37 := rwrtTac36; repeat rwrtTac_A37; repeat rwrtTac_B37.

Ltac t315 :=
  t_base ||
  List_tactic36 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t316 :=
  t315 ||
  rwrtTac37 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t316.

(***********************
  End of :+
 ***********************)
