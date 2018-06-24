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

Ltac t657 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t658 :=
  t657 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t658.


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

Lemma None_exists: (forall T: Type, forall self504: Option T, ((true = isNone T self504)) <-> (((None_construct T = self504)))). 
Proof.
	repeat t658 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self505: Option T, ((true = isSome T self505)) <-> ((exists tmp189: T, (Some_construct T tmp189 = self505)))). 
Proof.
	repeat t658 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic63 := match goal with 
	| [ H252: (true = isNone ?T ?self506) |- _ ] => 
			poseNew (Mark (T,self506) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H252)
	| [ H252: (isNone ?T ?self506 = true) |- _ ] => 
			poseNew (Mark (T,self506) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H252))
	| [ H253: (true = isSome ?T ?self507) |- _ ] => 
			poseNew (Mark (T,self507) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H253)
	| [ H253: (isSome ?T ?self507 = true) |- _ ] => 
			poseNew (Mark (T,self507) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H253))
	| _ => idtac
end.

Ltac t659 :=
  t_base ||
  Option_tactic63 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t660 :=
  t659 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t660.


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

Lemma Cons_exists: (forall T: Type, forall self508: List T, ((true = isCons T self508)) <-> ((exists tmp191: List T, exists tmp190: T, (Cons_construct T tmp190 tmp191 = self508)))). 
Proof.
	repeat t660 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self509: List T, ((true = isNil T self509)) <-> (((Nil_construct T = self509)))). 
Proof.
	repeat t660 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic63 := match goal with 
	| [ H254: (true = isCons ?T ?self510) |- _ ] => 
			poseNew (Mark (T,self510) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H254)
	| [ H254: (isCons ?T ?self510 = true) |- _ ] => 
			poseNew (Mark (T,self510) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H254))
	| [ H255: (true = isNil ?T ?self511) |- _ ] => 
			poseNew (Mark (T,self511) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H255)
	| [ H255: (isNil ?T ?self511 = true) |- _ ] => 
			poseNew (Mark (T,self511) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H255))
	| _ => Option_tactic63
end.

Ltac t661 :=
  t_base ||
  List_tactic63 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t662 :=
  t661 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t662.

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
  Start of tails
 ***********************)


Definition tails_rt_type (T: Type) (l5: List T) : Type :=
List (List T).

Fail Next Obligation.

Hint Unfold tails_rt_type.


Equations (noind) tails (T: Type) (l5: List T) : tails_rt_type T l5 := 
	tails T l5 by rec ignore_termination lt :=
	tails T l5 := match l5 with
	| Cons_construct _ _ tl => Cons_construct (List T) tl (tails T tl)
	| Nil_construct _ => 
			Cons_construct (List T) (Nil_construct T) (Nil_construct (List T))
	end.

Hint Unfold tails_comp_proj.

Solve Obligations with (repeat t662).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A125 := match goal with 
	| [ H1381: context[tails ?T ?l5] |- _ ] => 
			poseNew (Mark (T,l5) "unfolding tails_equation")
	| [  |- context[tails ?T ?l5] ] => poseNew (Mark (T,l5) "unfolding tails_equation")
end.

Ltac rwrtTac_B125 := match goal with 
	| [ H1381: context[tails ?T ?l5], H2381: Marked (?T,?l5) "unfolding tails_equation" |- _ ] => 
			poseNew (Mark (T,l5) "unfolded tails_equation");
			add_equation (tails_equation_1 T l5)
	| [ H2381: Marked (?T,?l5) "unfolding tails_equation" |- context[tails ?T ?l5] ] => 
			poseNew (Mark (T,l5) "unfolded tails_equation");
			add_equation (tails_equation_1 T l5)
end.

Ltac rwrtTac125 := idtac; repeat rwrtTac_A125; repeat rwrtTac_B125.

Ltac t663 :=
  t_base ||
  List_tactic63 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t664 :=
  t663 ||
  rwrtTac125 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t664.

(***********************
  End of tails
 ***********************)
