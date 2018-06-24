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

Ltac t615 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t616 :=
  t615 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t616.


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

Lemma None_exists: (forall T: Type, forall self472: Option T, ((true = isNone T self472)) <-> (((None_construct T = self472)))). 
Proof.
	repeat t616 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self473: Option T, ((true = isSome T self473)) <-> ((exists tmp177: T, (Some_construct T tmp177 = self473)))). 
Proof.
	repeat t616 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic59 := match goal with 
	| [ H236: (true = isNone ?T ?self474) |- _ ] => 
			poseNew (Mark (T,self474) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H236)
	| [ H236: (isNone ?T ?self474 = true) |- _ ] => 
			poseNew (Mark (T,self474) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H236))
	| [ H237: (true = isSome ?T ?self475) |- _ ] => 
			poseNew (Mark (T,self475) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H237)
	| [ H237: (isSome ?T ?self475 = true) |- _ ] => 
			poseNew (Mark (T,self475) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H237))
	| _ => idtac
end.

Ltac t617 :=
  t_base ||
  Option_tactic59 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t618 :=
  t617 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t618.


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

Lemma Cons_exists: (forall T: Type, forall self476: List T, ((true = isCons T self476)) <-> ((exists tmp179: List T, exists tmp178: T, (Cons_construct T tmp178 tmp179 = self476)))). 
Proof.
	repeat t618 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self477: List T, ((true = isNil T self477)) <-> (((Nil_construct T = self477)))). 
Proof.
	repeat t618 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic59 := match goal with 
	| [ H238: (true = isCons ?T ?self478) |- _ ] => 
			poseNew (Mark (T,self478) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H238)
	| [ H238: (isCons ?T ?self478 = true) |- _ ] => 
			poseNew (Mark (T,self478) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H238))
	| [ H239: (true = isNil ?T ?self479) |- _ ] => 
			poseNew (Mark (T,self479) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H239)
	| [ H239: (isNil ?T ?self479 = true) |- _ ] => 
			poseNew (Mark (T,self479) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H239))
	| _ => Option_tactic59
end.

Ltac t619 :=
  t_base ||
  List_tactic59 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t620 :=
  t619 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t620.

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
  Start of head
 ***********************)

Definition head (T: Type) (thiss14: List T) (contractHyp176: (negb (propInBool ((thiss14 = Nil_construct T))) = true)) : T :=
ifthenelse (isCons _ thiss14) T
	(fun _ => h T thiss14 )
	(fun _ => let contradiction: False := _ in match contradiction with end ).

Fail Next Obligation.

Hint Unfold head: definitions.

(***********************
  End of head
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt27_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt27_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt27_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A117 := match goal with 
	| [ H1357: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B117 := match goal with 
	| [ H1357: context[size ?T ?thiss30], H2357: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2357: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac117 := idtac; repeat rwrtTac_A117; repeat rwrtTac_B117.

Ltac t621 :=
  t_base ||
  List_tactic59 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t622 :=
  t621 ||
  rwrtTac117 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t622.

(***********************
  End of size
 ***********************)

(***********************
  Start of tail
 ***********************)

Definition tail (T: Type) (thiss56: List T) (contractHyp178: (negb (propInBool ((thiss56 = Nil_construct T))) = true)) : List T :=
ifthenelse (isCons _ thiss56) (List T)
	(fun _ => t7 T thiss56 )
	(fun _ => let contradiction: False := _ in match contradiction with end ).

Fail Next Obligation.

Hint Unfold tail: definitions.

(***********************
  End of tail
 ***********************)


(***********************
  Start of apply
 ***********************)


Definition contractHyp179_type (T: Type) (thiss57: List T) (index: Z) : Type :=
(ifthenelse (Z.leb (0)%Z index) bool
	(fun _ => Z.ltb index (proj1_sig (size T thiss57)) )
	(fun _ => false ) = true).

Fail Next Obligation.

Hint Unfold contractHyp179_type.


Definition apply_rt_type (T: Type) (thiss57: List T) (index: Z) (contractHyp179: contractHyp179_type T thiss57 index) : Type :=
T.

Fail Next Obligation.

Hint Unfold apply_rt_type.


Equations (noind) apply (T: Type) (thiss57: List T) (index: Z) (contractHyp179: contractHyp179_type T thiss57 index) : apply_rt_type T thiss57 index contractHyp179 := 
	apply T thiss57 index contractHyp179 by rec ignore_termination lt :=
	apply T thiss57 index contractHyp179 := ifthenelse (Zeq_bool index (0)%Z) T
		(fun _ => head T thiss57 _ )
		(fun _ => apply T (tail T thiss57 _) (Z.sub index (1)%Z) _ ).

Hint Unfold apply_comp_proj.

Solve Obligations with (repeat t622).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A118 := match goal with 
	| [ H1358: context[apply ?T ?thiss57 ?index] |- _ ] => 
			poseNew (Mark (T,thiss57,index) "unfolding apply_equation")
	| [  |- context[apply ?T ?thiss57 ?index] ] => 
			poseNew (Mark (T,thiss57,index) "unfolding apply_equation")
end.

Ltac rwrtTac_B118 := match goal with 
	| [ H1358: context[apply ?T ?thiss57 ?index], H2358: Marked (?T,?thiss57,?index) "unfolding apply_equation" |- _ ] => 
			poseNew (Mark (T,thiss57,index) "unfolded apply_equation");
			add_equation (apply_equation_1 T thiss57 index)
	| [ H2358: Marked (?T,?thiss57,?index) "unfolding apply_equation" |- context[apply ?T ?thiss57 ?index] ] => 
			poseNew (Mark (T,thiss57,index) "unfolded apply_equation");
			add_equation (apply_equation_1 T thiss57 index)
end.

Ltac rwrtTac118 := rwrtTac117; repeat rwrtTac_A118; repeat rwrtTac_B118.

Ltac t623 :=
  t_base ||
  List_tactic59 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t624 :=
  t623 ||
  rwrtTac118 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t624.

(***********************
  End of apply
 ***********************)
