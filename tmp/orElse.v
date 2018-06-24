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

Ltac t207 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t208 :=
  t207 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t208.


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

Lemma None_exists: (forall T: Type, forall self216: Option T, ((true = isNone T self216)) <-> (((None_construct T = self216)))). 
Proof.
	repeat t208 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self217: Option T, ((true = isSome T self217)) <-> ((exists tmp81: T, (Some_construct T tmp81 = self217)))). 
Proof.
	repeat t208 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic27 := match goal with 
	| [ H108: (true = isNone ?T ?self218) |- _ ] => 
			poseNew (Mark (T,self218) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H108)
	| [ H108: (isNone ?T ?self218 = true) |- _ ] => 
			poseNew (Mark (T,self218) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H108))
	| [ H109: (true = isSome ?T ?self219) |- _ ] => 
			poseNew (Mark (T,self219) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H109)
	| [ H109: (isSome ?T ?self219 = true) |- _ ] => 
			poseNew (Mark (T,self219) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H109))
	| _ => idtac
end.

Ltac t209 :=
  t_base ||
  Option_tactic27 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t210 :=
  t209 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t210.


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

Lemma Cons_exists: (forall T: Type, forall self220: List T, ((true = isCons T self220)) <-> ((exists tmp83: List T, exists tmp82: T, (Cons_construct T tmp82 tmp83 = self220)))). 
Proof.
	repeat t210 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self221: List T, ((true = isNil T self221)) <-> (((Nil_construct T = self221)))). 
Proof.
	repeat t210 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic27 := match goal with 
	| [ H110: (true = isCons ?T ?self222) |- _ ] => 
			poseNew (Mark (T,self222) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H110)
	| [ H110: (isCons ?T ?self222 = true) |- _ ] => 
			poseNew (Mark (T,self222) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H110))
	| [ H111: (true = isNil ?T ?self223) |- _ ] => 
			poseNew (Mark (T,self223) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H111)
	| [ H111: (isNil ?T ?self223 = true) |- _ ] => 
			poseNew (Mark (T,self223) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H111))
	| _ => Option_tactic27
end.

Ltac t211 :=
  t_base ||
  List_tactic27 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t212 :=
  t211 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t212.

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
  Start of isEmpty
 ***********************)

Definition isEmpty1 (T: Type) (thiss18: Option T) : bool :=
propInBool ((thiss18 = None_construct T)).

Fail Next Obligation.

Hint Unfold isEmpty1: definitions.

(***********************
  End of isEmpty
 ***********************)

(***********************
  Start of isDefined
 ***********************)

Definition isDefined (T: Type) (thiss19: Option T) : bool :=
negb (isEmpty1 T thiss19).

Fail Next Obligation.

Hint Unfold isDefined: definitions.

(***********************
  End of isDefined
 ***********************)


(***********************
  Start of orElse
 ***********************)

Definition orElse (T: Type) (thiss26: Option T) (or: Option T) : {x___1: Option T | (ifthenelse (Bool.eqb (isDefined T x___1) (isDefined T thiss26)) bool
	(fun _ => true )
	(fun _ => isDefined T or ) = true)} :=
match thiss26 with
| Some_construct _ v4 => thiss26
| None_construct _ => or
end.

Fail Next Obligation.

Hint Unfold orElse: definitions.

(***********************
  End of orElse
 ***********************)
