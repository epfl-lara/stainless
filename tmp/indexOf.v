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

Ltac t126 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t127 :=
  t126 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t127.


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

Lemma None_exists: (forall T: Type, forall self128: Option T, ((true = isNone T self128)) <-> (((None_construct T = self128)))). 
Proof.
	repeat t127 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self129: Option T, ((true = isSome T self129)) <-> ((exists tmp48: T, (Some_construct T tmp48 = self129)))). 
Proof.
	repeat t127 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic16 := match goal with 
	| [ H64: (true = isNone ?T ?self130) |- _ ] => 
			poseNew (Mark (T,self130) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H64)
	| [ H64: (isNone ?T ?self130 = true) |- _ ] => 
			poseNew (Mark (T,self130) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H64))
	| [ H65: (true = isSome ?T ?self131) |- _ ] => 
			poseNew (Mark (T,self131) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H65)
	| [ H65: (isSome ?T ?self131 = true) |- _ ] => 
			poseNew (Mark (T,self131) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H65))
	| _ => idtac
end.

Ltac t128 :=
  t_base ||
  Option_tactic16 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t129 :=
  t128 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t129.


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

Lemma Cons_exists: (forall T: Type, forall self132: List T, ((true = isCons T self132)) <-> ((exists tmp50: List T, exists tmp49: T, (Cons_construct T tmp49 tmp50 = self132)))). 
Proof.
	repeat t129 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self133: List T, ((true = isNil T self133)) <-> (((Nil_construct T = self133)))). 
Proof.
	repeat t129 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic16 := match goal with 
	| [ H66: (true = isCons ?T ?self134) |- _ ] => 
			poseNew (Mark (T,self134) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H66)
	| [ H66: (isCons ?T ?self134 = true) |- _ ] => 
			poseNew (Mark (T,self134) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H66))
	| [ H67: (true = isNil ?T ?self135) |- _ ] => 
			poseNew (Mark (T,self135) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H67)
	| [ H67: (isNil ?T ?self135 = true) |- _ ] => 
			poseNew (Mark (T,self135) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H67))
	| _ => Option_tactic16
end.

Ltac t130 :=
  t_base ||
  List_tactic16 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t131 :=
  t130 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t131.

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
Definition content_rt3_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt3_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt3_type T thiss1 := 
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

Ltac rwrtTac_A10 := match goal with 
	| [ H178: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B10 := match goal with 
	| [ H178: context[content ?T ?thiss1], H278: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H278: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac10 := idtac; repeat rwrtTac_A10; repeat rwrtTac_B10.

Ltac t132 :=
  t_base ||
  List_tactic16 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t133 :=
  t132 ||
  rwrtTac10 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t133.

(***********************
  End of content
 ***********************)


(***********************
  Start of indexOf
 ***********************)


Definition indexOf_rt_type (T: Type) (thiss15: List T) (elem: T) : Type :=
{res1: Z | (Bool.eqb (Z.geb res1 (0)%Z) (set_elem_of elem (content T thiss15)) = true)}.

Fail Next Obligation.

Hint Unfold indexOf_rt_type.


Equations (noind) indexOf (T: Type) (thiss15: List T) (elem: T) : indexOf_rt_type T thiss15 elem := 
	indexOf T thiss15 elem by rec ignore_termination lt :=
	indexOf T thiss15 elem := ifthenelse (isNil _ thiss15) Z
		(fun _ => (-1)%Z )
		(fun _ => ifthenelse
			(ifthenelse (isCons _ thiss15) bool
				(fun _ => propInBool ((h T thiss15 = elem)) )
				(fun _ => false ))
			Z
			(fun _ => (0)%Z )
			(fun _ => ifthenelse (isCons _ thiss15) Z
				(fun _ => let rec := (proj1_sig (indexOf T (t7 T thiss15) elem)) in (ifthenelse (Zeq_bool rec (-1)%Z) Z
					(fun _ => (-1)%Z )
					(fun _ => Z.add rec (1)%Z )) )
				(fun _ => let contradiction: False := _ in match contradiction with end ) ) ).

Hint Unfold indexOf_comp_proj.

Solve Obligations with (repeat t133).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A11 := match goal with 
	| [ H179: context[indexOf ?T ?thiss15 ?elem] |- _ ] => 
			poseNew (Mark (T,thiss15,elem) "unfolding indexOf_equation")
	| [  |- context[indexOf ?T ?thiss15 ?elem] ] => 
			poseNew (Mark (T,thiss15,elem) "unfolding indexOf_equation")
end.

Ltac rwrtTac_B11 := match goal with 
	| [ H179: context[indexOf ?T ?thiss15 ?elem], H279: Marked (?T,?thiss15,?elem) "unfolding indexOf_equation" |- _ ] => 
			poseNew (Mark (T,thiss15,elem) "unfolded indexOf_equation");
			add_equation (indexOf_equation_1 T thiss15 elem)
	| [ H279: Marked (?T,?thiss15,?elem) "unfolding indexOf_equation" |- context[indexOf ?T ?thiss15 ?elem] ] => 
			poseNew (Mark (T,thiss15,elem) "unfolded indexOf_equation");
			add_equation (indexOf_equation_1 T thiss15 elem)
end.

Ltac rwrtTac11 := rwrtTac10; repeat rwrtTac_A11; repeat rwrtTac_B11.

Ltac t134 :=
  t_base ||
  List_tactic16 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t135 :=
  t134 ||
  rwrtTac11 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t135.

(***********************
  End of indexOf
 ***********************)
