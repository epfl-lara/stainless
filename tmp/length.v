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

Ltac t485 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t486 :=
  t485 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t486.


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

Lemma None_exists: (forall T: Type, forall self392: Option T, ((true = isNone T self392)) <-> (((None_construct T = self392)))). 
Proof.
	repeat t486 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self393: Option T, ((true = isSome T self393)) <-> ((exists tmp147: T, (Some_construct T tmp147 = self393)))). 
Proof.
	repeat t486 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic49 := match goal with 
	| [ H196: (true = isNone ?T ?self394) |- _ ] => 
			poseNew (Mark (T,self394) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H196)
	| [ H196: (isNone ?T ?self394 = true) |- _ ] => 
			poseNew (Mark (T,self394) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H196))
	| [ H197: (true = isSome ?T ?self395) |- _ ] => 
			poseNew (Mark (T,self395) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H197)
	| [ H197: (isSome ?T ?self395 = true) |- _ ] => 
			poseNew (Mark (T,self395) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H197))
	| _ => idtac
end.

Ltac t487 :=
  t_base ||
  Option_tactic49 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t488 :=
  t487 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t488.


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

Lemma Cons_exists: (forall T: Type, forall self396: List T, ((true = isCons T self396)) <-> ((exists tmp149: List T, exists tmp148: T, (Cons_construct T tmp148 tmp149 = self396)))). 
Proof.
	repeat t488 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self397: List T, ((true = isNil T self397)) <-> (((Nil_construct T = self397)))). 
Proof.
	repeat t488 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic49 := match goal with 
	| [ H198: (true = isCons ?T ?self398) |- _ ] => 
			poseNew (Mark (T,self398) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H198)
	| [ H198: (isCons ?T ?self398 = true) |- _ ] => 
			poseNew (Mark (T,self398) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H198))
	| [ H199: (true = isNil ?T ?self399) |- _ ] => 
			poseNew (Mark (T,self399) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H199)
	| [ H199: (isNil ?T ?self399 = true) |- _ ] => 
			poseNew (Mark (T,self399) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H199))
	| _ => Option_tactic49
end.

Ltac t489 :=
  t_base ||
  List_tactic49 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t490 :=
  t489 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t490.

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
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt18_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt18_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt18_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A84 := match goal with 
	| [ H1284: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B84 := match goal with 
	| [ H1284: context[size ?T ?thiss30], H2284: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2284: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac84 := idtac; repeat rwrtTac_A84; repeat rwrtTac_B84.

Ltac t491 :=
  t_base ||
  List_tactic49 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t492 :=
  t491 ||
  rwrtTac84 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t492.

(***********************
  End of size
 ***********************)


(***********************
  Start of length
 ***********************)

Definition length (T: Type) (thiss47: List T) : Z :=
proj1_sig (size T thiss47).

Fail Next Obligation.

Hint Unfold length: definitions.

(***********************
  End of length
 ***********************)
