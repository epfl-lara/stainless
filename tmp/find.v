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

Ltac t41 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t42 :=
  t41 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t42.


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

Lemma None_exists: (forall T: Type, forall self40: Option T, ((true = isNone T self40)) <-> (((None_construct T = self40)))). 
Proof.
	repeat t42 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self41: Option T, ((true = isSome T self41)) <-> ((exists tmp15: T, (Some_construct T tmp15 = self41)))). 
Proof.
	repeat t42 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic5 := match goal with 
	| [ H20: (true = isNone ?T ?self42) |- _ ] => 
			poseNew (Mark (T,self42) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H20)
	| [ H20: (isNone ?T ?self42 = true) |- _ ] => 
			poseNew (Mark (T,self42) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H20))
	| [ H21: (true = isSome ?T ?self43) |- _ ] => 
			poseNew (Mark (T,self43) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H21)
	| [ H21: (isSome ?T ?self43 = true) |- _ ] => 
			poseNew (Mark (T,self43) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H21))
	| _ => idtac
end.

Ltac t43 :=
  t_base ||
  Option_tactic5 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t44 :=
  t43 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t44.


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

Lemma Cons_exists: (forall T: Type, forall self44: List T, ((true = isCons T self44)) <-> ((exists tmp17: List T, exists tmp16: T, (Cons_construct T tmp16 tmp17 = self44)))). 
Proof.
	repeat t44 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self45: List T, ((true = isNil T self45)) <-> (((Nil_construct T = self45)))). 
Proof.
	repeat t44 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic5 := match goal with 
	| [ H22: (true = isCons ?T ?self46) |- _ ] => 
			poseNew (Mark (T,self46) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H22)
	| [ H22: (isCons ?T ?self46 = true) |- _ ] => 
			poseNew (Mark (T,self46) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H22))
	| [ H23: (true = isNil ?T ?self47) |- _ ] => 
			poseNew (Mark (T,self47) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H23)
	| [ H23: (isNil ?T ?self47 = true) |- _ ] => 
			poseNew (Mark (T,self47) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H23))
	| _ => Option_tactic5
end.

Ltac t45 :=
  t_base ||
  List_tactic5 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t46 :=
  t45 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t46.

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
Definition content_rt2_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt2_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt2_type T thiss1 := 
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

Ltac rwrtTac_A3 := match goal with 
	| [ H127: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B3 := match goal with 
	| [ H127: context[content ?T ?thiss1], H227: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H227: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac3 := idtac; repeat rwrtTac_A3; repeat rwrtTac_B3.

Ltac t47 :=
  t_base ||
  List_tactic5 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t48 :=
  t47 ||
  rwrtTac3 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t48.

(***********************
  End of content
 ***********************)


(***********************
  Start of find
 ***********************)


Definition find_rt_type (T: Type) (thiss4: List T) (p1: T -> bool) : Type :=
{res: Option T | (match res with
| Some_construct _ r => 
		ifthenelse (set_elem_of r (content T thiss4)) bool
			(fun _ => p1 r )
			(fun _ => false )
| None_construct _ => true
end = true)}.

Fail Next Obligation.

Hint Unfold find_rt_type.


Equations (noind) find (T: Type) (thiss4: List T) (p1: T -> bool) : find_rt_type T thiss4 p1 := 
	find T thiss4 p1 by rec ignore_termination lt :=
	find T thiss4 p1 := match thiss4 with
	| Nil_construct _ => None_construct T
	| Cons_construct _ h3 t49 => 
			ifthenelse (p1 h3) (Option T)
				(fun _ => Some_construct T h3 )
				(fun _ => proj1_sig (find T t49 p1) )
	end.

Hint Unfold find_comp_proj.

Solve Obligations with (repeat t48).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A4 := match goal with 
	| [ H128: context[find ?T ?thiss4 ?p1] |- _ ] => 
			poseNew (Mark (T,thiss4,p1) "unfolding find_equation")
	| [  |- context[find ?T ?thiss4 ?p1] ] => 
			poseNew (Mark (T,thiss4,p1) "unfolding find_equation")
end.

Ltac rwrtTac_B4 := match goal with 
	| [ H128: context[find ?T ?thiss4 ?p1], H228: Marked (?T,?thiss4,?p1) "unfolding find_equation" |- _ ] => 
			poseNew (Mark (T,thiss4,p1) "unfolded find_equation");
			add_equation (find_equation_1 T thiss4 p1)
	| [ H228: Marked (?T,?thiss4,?p1) "unfolding find_equation" |- context[find ?T ?thiss4 ?p1] ] => 
			poseNew (Mark (T,thiss4,p1) "unfolded find_equation");
			add_equation (find_equation_1 T thiss4 p1)
end.

Ltac rwrtTac4 := rwrtTac3; repeat rwrtTac_A4; repeat rwrtTac_B4.

Ltac t50 :=
  t_base ||
  List_tactic5 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t51 :=
  t50 ||
  rwrtTac4 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t51.

(***********************
  End of find
 ***********************)
