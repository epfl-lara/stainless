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

Ltac t753 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t754 :=
  t753 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t754.


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

Lemma None_exists: (forall T: Type, forall self560: Option T, ((true = isNone T self560)) <-> (((None_construct T = self560)))). 
Proof.
	repeat t754 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self561: Option T, ((true = isSome T self561)) <-> ((exists tmp210: T, (Some_construct T tmp210 = self561)))). 
Proof.
	repeat t754 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic70 := match goal with 
	| [ H280: (true = isNone ?T ?self562) |- _ ] => 
			poseNew (Mark (T,self562) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H280)
	| [ H280: (isNone ?T ?self562 = true) |- _ ] => 
			poseNew (Mark (T,self562) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H280))
	| [ H281: (true = isSome ?T ?self563) |- _ ] => 
			poseNew (Mark (T,self563) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H281)
	| [ H281: (isSome ?T ?self563 = true) |- _ ] => 
			poseNew (Mark (T,self563) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H281))
	| _ => idtac
end.

Ltac t755 :=
  t_base ||
  Option_tactic70 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t756 :=
  t755 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t756.


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

Lemma Cons_exists: (forall T: Type, forall self564: List T, ((true = isCons T self564)) <-> ((exists tmp212: List T, exists tmp211: T, (Cons_construct T tmp211 tmp212 = self564)))). 
Proof.
	repeat t756 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self565: List T, ((true = isNil T self565)) <-> (((Nil_construct T = self565)))). 
Proof.
	repeat t756 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic70 := match goal with 
	| [ H282: (true = isCons ?T ?self566) |- _ ] => 
			poseNew (Mark (T,self566) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H282)
	| [ H282: (isCons ?T ?self566 = true) |- _ ] => 
			poseNew (Mark (T,self566) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H282))
	| [ H283: (true = isNil ?T ?self567) |- _ ] => 
			poseNew (Mark (T,self567) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H283)
	| [ H283: (isNil ?T ?self567 = true) |- _ ] => 
			poseNew (Mark (T,self567) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H283))
	| _ => Option_tactic70
end.

Ltac t757 :=
  t_base ||
  List_tactic70 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t758 :=
  t757 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t758.

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
  Start of toSet
 ***********************)

Definition toSet (T: Type) (thiss67: Option T) : set (T) :=
match thiss67 with
| None_construct _ => @set_empty T
| Some_construct _ x5 => set_union (@set_empty T) (set_singleton x5)
end.

Fail Next Obligation.

Hint Unfold toSet: definitions.

(***********************
  End of toSet
 ***********************)
