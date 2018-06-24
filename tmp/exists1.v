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

Ltac t99 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t100 :=
  t99 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t100.


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

Lemma None_exists: (forall T: Type, forall self96: Option T, ((true = isNone T self96)) <-> (((None_construct T = self96)))). 
Proof.
	repeat t100 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self97: Option T, ((true = isSome T self97)) <-> ((exists tmp36: T, (Some_construct T tmp36 = self97)))). 
Proof.
	repeat t100 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic12 := match goal with 
	| [ H48: (true = isNone ?T ?self98) |- _ ] => 
			poseNew (Mark (T,self98) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H48)
	| [ H48: (isNone ?T ?self98 = true) |- _ ] => 
			poseNew (Mark (T,self98) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H48))
	| [ H49: (true = isSome ?T ?self99) |- _ ] => 
			poseNew (Mark (T,self99) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H49)
	| [ H49: (isSome ?T ?self99 = true) |- _ ] => 
			poseNew (Mark (T,self99) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H49))
	| _ => idtac
end.

Ltac t101 :=
  t_base ||
  Option_tactic12 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t102 :=
  t101 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t102.


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

Lemma Cons_exists: (forall T: Type, forall self100: List T, ((true = isCons T self100)) <-> ((exists tmp38: List T, exists tmp37: T, (Cons_construct T tmp37 tmp38 = self100)))). 
Proof.
	repeat t102 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self101: List T, ((true = isNil T self101)) <-> (((Nil_construct T = self101)))). 
Proof.
	repeat t102 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic12 := match goal with 
	| [ H50: (true = isCons ?T ?self102) |- _ ] => 
			poseNew (Mark (T,self102) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H50)
	| [ H50: (isCons ?T ?self102 = true) |- _ ] => 
			poseNew (Mark (T,self102) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H50))
	| [ H51: (true = isNil ?T ?self103) |- _ ] => 
			poseNew (Mark (T,self103) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H51)
	| [ H51: (isNil ?T ?self103 = true) |- _ ] => 
			poseNew (Mark (T,self103) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H51))
	| _ => Option_tactic12
end.

Ltac t103 :=
  t_base ||
  List_tactic12 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t104 :=
  t103 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t104.

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
  Start of forall
 ***********************)

Definition forall1 (T: Type) (thiss10: Option T) (p4: T -> bool) : bool :=
ifthenelse
	(ifthenelse (isSome _ thiss10) bool
		(fun _ => negb (p4 (v T thiss10)) )
		(fun _ => false ))
	bool
	(fun _ => false )
	(fun _ => true ).

Fail Next Obligation.

Hint Unfold forall1: definitions.

(***********************
  End of forall
 ***********************)


(***********************
  Start of exists
 ***********************)

Definition exists1 (T: Type) (thiss11: Option T) (p5: T -> bool) : bool :=
negb (forall1 T thiss11 (fun x___3 => negb (p5 x___3) )).

Fail Next Obligation.

Hint Unfold exists1: definitions.

(***********************
  End of exists
 ***********************)
