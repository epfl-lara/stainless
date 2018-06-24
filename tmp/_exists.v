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

Ltac t85 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t86 :=
  t85 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t86.


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

Lemma None_exists: (forall T: Type, forall self80: Option T, ((true = isNone T self80)) <-> (((None_construct T = self80)))). 
Proof.
	repeat t86 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self81: Option T, ((true = isSome T self81)) <-> ((exists tmp30: T, (Some_construct T tmp30 = self81)))). 
Proof.
	repeat t86 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic10 := match goal with 
	| [ H40: (true = isNone ?T ?self82) |- _ ] => 
			poseNew (Mark (T,self82) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H40)
	| [ H40: (isNone ?T ?self82 = true) |- _ ] => 
			poseNew (Mark (T,self82) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H40))
	| [ H41: (true = isSome ?T ?self83) |- _ ] => 
			poseNew (Mark (T,self83) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H41)
	| [ H41: (isSome ?T ?self83 = true) |- _ ] => 
			poseNew (Mark (T,self83) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H41))
	| _ => idtac
end.

Ltac t87 :=
  t_base ||
  Option_tactic10 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t88 :=
  t87 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t88.


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

Lemma Cons_exists: (forall T: Type, forall self84: List T, ((true = isCons T self84)) <-> ((exists tmp32: List T, exists tmp31: T, (Cons_construct T tmp31 tmp32 = self84)))). 
Proof.
	repeat t88 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self85: List T, ((true = isNil T self85)) <-> (((Nil_construct T = self85)))). 
Proof.
	repeat t88 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic10 := match goal with 
	| [ H42: (true = isCons ?T ?self86) |- _ ] => 
			poseNew (Mark (T,self86) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H42)
	| [ H42: (isCons ?T ?self86 = true) |- _ ] => 
			poseNew (Mark (T,self86) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H42))
	| [ H43: (true = isNil ?T ?self87) |- _ ] => 
			poseNew (Mark (T,self87) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H43)
	| [ H43: (isNil ?T ?self87 = true) |- _ ] => 
			poseNew (Mark (T,self87) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H43))
	| _ => Option_tactic10
end.

Ltac t89 :=
  t_base ||
  List_tactic10 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t90 :=
  t89 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t90.

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

Obligation Tactic:=idtac.
Definition _forall_rt1_type (T: Type) (thiss8: List T) (p2: T -> bool) : Type :=
bool.

Fail Next Obligation.

Hint Unfold _forall_rt1_type.


Equations (noind) _forall (T: Type) (thiss8: List T) (p2: T -> bool) : _forall_rt1_type T thiss8 p2 := 
	_forall T thiss8 p2 by rec ignore_termination lt :=
	_forall T thiss8 p2 := match thiss8 with
	| Nil_construct _ => true
	| Cons_construct _ h6 t82 => 
			ifthenelse (p2 h6) bool
				(fun _ => _forall T t82 p2 )
				(fun _ => false )
	end.

Hint Unfold _forall_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A8 := match goal with 
	| [ H152: context[_forall ?T ?thiss8 ?p2] |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
	| [  |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
end.

Ltac rwrtTac_B8 := match goal with 
	| [ H152: context[_forall ?T ?thiss8 ?p2], H252: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
	| [ H252: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
end.

Ltac rwrtTac8 := idtac; repeat rwrtTac_A8; repeat rwrtTac_B8.

Ltac t91 :=
  t_base ||
  List_tactic10 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t92 :=
  t91 ||
  rwrtTac8 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t92.

(***********************
  End of forall
 ***********************)


(***********************
  Start of exists
 ***********************)

Definition _exists (T: Type) (thiss9: List T) (p3: T -> bool) : bool :=
negb (_forall T thiss9 (fun x___22 => negb (p3 x___22) )).

Fail Next Obligation.

Hint Unfold _exists: definitions.

(***********************
  End of exists
 ***********************)
