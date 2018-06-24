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

Ltac t650 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t651 :=
  t650 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t651.


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

Lemma None_exists: (forall T: Type, forall self496: Option T, ((true = isNone T self496)) <-> (((None_construct T = self496)))). 
Proof.
	repeat t651 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self497: Option T, ((true = isSome T self497)) <-> ((exists tmp186: T, (Some_construct T tmp186 = self497)))). 
Proof.
	repeat t651 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic62 := match goal with 
	| [ H248: (true = isNone ?T ?self498) |- _ ] => 
			poseNew (Mark (T,self498) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H248)
	| [ H248: (isNone ?T ?self498 = true) |- _ ] => 
			poseNew (Mark (T,self498) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H248))
	| [ H249: (true = isSome ?T ?self499) |- _ ] => 
			poseNew (Mark (T,self499) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H249)
	| [ H249: (isSome ?T ?self499 = true) |- _ ] => 
			poseNew (Mark (T,self499) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H249))
	| _ => idtac
end.

Ltac t652 :=
  t_base ||
  Option_tactic62 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t653 :=
  t652 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t653.


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

Lemma Cons_exists: (forall T: Type, forall self500: List T, ((true = isCons T self500)) <-> ((exists tmp188: List T, exists tmp187: T, (Cons_construct T tmp187 tmp188 = self500)))). 
Proof.
	repeat t653 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self501: List T, ((true = isNil T self501)) <-> (((Nil_construct T = self501)))). 
Proof.
	repeat t653 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic62 := match goal with 
	| [ H250: (true = isCons ?T ?self502) |- _ ] => 
			poseNew (Mark (T,self502) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H250)
	| [ H250: (isCons ?T ?self502 = true) |- _ ] => 
			poseNew (Mark (T,self502) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H250))
	| [ H251: (true = isNil ?T ?self503) |- _ ] => 
			poseNew (Mark (T,self503) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H251)
	| [ H251: (isNil ?T ?self503 = true) |- _ ] => 
			poseNew (Mark (T,self503) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H251))
	| _ => Option_tactic62
end.

Ltac t654 :=
  t_base ||
  List_tactic62 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t655 :=
  t654 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t655.

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
  Start of tailOption
 ***********************)

Definition tailOption (T: Type) (thiss60: List T) : {x___6: Option (List T) | (negb (Bool.eqb (isDefined (List T) x___6) (isEmpty T thiss60)) = true)} :=
match thiss60 with
| Cons_construct _ h25 t656 => Some_construct (List T) t656
| Nil_construct _ => None_construct (List T)
end.

Fail Next Obligation.

Hint Unfold tailOption: definitions.

(***********************
  End of tailOption
 ***********************)
