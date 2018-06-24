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

Ltac t76 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t77 :=
  t76 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t77.


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

Lemma None_exists: (forall T: Type, forall self72: Option T, ((true = isNone T self72)) <-> (((None_construct T = self72)))). 
Proof.
	repeat t77 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self73: Option T, ((true = isSome T self73)) <-> ((exists tmp27: T, (Some_construct T tmp27 = self73)))). 
Proof.
	repeat t77 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic9 := match goal with 
	| [ H36: (true = isNone ?T ?self74) |- _ ] => 
			poseNew (Mark (T,self74) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H36)
	| [ H36: (isNone ?T ?self74 = true) |- _ ] => 
			poseNew (Mark (T,self74) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H36))
	| [ H37: (true = isSome ?T ?self75) |- _ ] => 
			poseNew (Mark (T,self75) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H37)
	| [ H37: (isSome ?T ?self75 = true) |- _ ] => 
			poseNew (Mark (T,self75) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H37))
	| _ => idtac
end.

Ltac t78 :=
  t_base ||
  Option_tactic9 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t79 :=
  t78 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t79.


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

Lemma Cons_exists: (forall T: Type, forall self76: List T, ((true = isCons T self76)) <-> ((exists tmp29: List T, exists tmp28: T, (Cons_construct T tmp28 tmp29 = self76)))). 
Proof.
	repeat t79 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self77: List T, ((true = isNil T self77)) <-> (((Nil_construct T = self77)))). 
Proof.
	repeat t79 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic9 := match goal with 
	| [ H38: (true = isCons ?T ?self78) |- _ ] => 
			poseNew (Mark (T,self78) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H38)
	| [ H38: (isCons ?T ?self78 = true) |- _ ] => 
			poseNew (Mark (T,self78) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H38))
	| [ H39: (true = isNil ?T ?self79) |- _ ] => 
			poseNew (Mark (T,self79) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H39)
	| [ H39: (isNil ?T ?self79 = true) |- _ ] => 
			poseNew (Mark (T,self79) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H39))
	| _ => Option_tactic9
end.

Ltac t80 :=
  t_base ||
  List_tactic9 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t81 :=
  t80 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t81.

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


Definition _forall_rt_type (T: Type) (thiss8: List T) (p2: T -> bool) : Type :=
bool.

Fail Next Obligation.

Hint Unfold _forall_rt_type.


Equations (noind) _forall (T: Type) (thiss8: List T) (p2: T -> bool) : _forall_rt_type T thiss8 p2 := 
	_forall T thiss8 p2 by rec ignore_termination lt :=
	_forall T thiss8 p2 := match thiss8 with
	| Nil_construct _ => true
	| Cons_construct _ h6 t82 => 
			ifthenelse (p2 h6) bool
				(fun _ => _forall T t82 p2 )
				(fun _ => false )
	end.

Hint Unfold _forall_comp_proj.

Solve Obligations with (repeat t81).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A7 := match goal with 
	| [ H147: context[_forall ?T ?thiss8 ?p2] |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
	| [  |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
end.

Ltac rwrtTac_B7 := match goal with 
	| [ H147: context[_forall ?T ?thiss8 ?p2], H247: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
	| [ H247: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
end.

Ltac rwrtTac7 := idtac; repeat rwrtTac_A7; repeat rwrtTac_B7.

Ltac t83 :=
  t_base ||
  List_tactic9 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t84 :=
  t83 ||
  rwrtTac7 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t84.

(***********************
  End of forall
 ***********************)
