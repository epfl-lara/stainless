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

Ltac t111 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t112 :=
  t111 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t112.


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

Lemma None_exists: (forall T: Type, forall self112: Option T, ((true = isNone T self112)) <-> (((None_construct T = self112)))). 
Proof.
	repeat t112 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self113: Option T, ((true = isSome T self113)) <-> ((exists tmp42: T, (Some_construct T tmp42 = self113)))). 
Proof.
	repeat t112 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic14 := match goal with 
	| [ H56: (true = isNone ?T ?self114) |- _ ] => 
			poseNew (Mark (T,self114) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H56)
	| [ H56: (isNone ?T ?self114 = true) |- _ ] => 
			poseNew (Mark (T,self114) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H56))
	| [ H57: (true = isSome ?T ?self115) |- _ ] => 
			poseNew (Mark (T,self115) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H57)
	| [ H57: (isSome ?T ?self115 = true) |- _ ] => 
			poseNew (Mark (T,self115) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H57))
	| _ => idtac
end.

Ltac t113 :=
  t_base ||
  Option_tactic14 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t114 :=
  t113 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t114.


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

Lemma Cons_exists: (forall T: Type, forall self116: List T, ((true = isCons T self116)) <-> ((exists tmp44: List T, exists tmp43: T, (Cons_construct T tmp43 tmp44 = self116)))). 
Proof.
	repeat t114 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self117: List T, ((true = isNil T self117)) <-> (((Nil_construct T = self117)))). 
Proof.
	repeat t114 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic14 := match goal with 
	| [ H58: (true = isCons ?T ?self118) |- _ ] => 
			poseNew (Mark (T,self118) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H58)
	| [ H58: (isCons ?T ?self118 = true) |- _ ] => 
			poseNew (Mark (T,self118) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H58))
	| [ H59: (true = isNil ?T ?self119) |- _ ] => 
			poseNew (Mark (T,self119) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H59)
	| [ H59: (isNil ?T ?self119 = true) |- _ ] => 
			poseNew (Mark (T,self119) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H59))
	| _ => Option_tactic14
end.

Ltac t115 :=
  t_base ||
  List_tactic14 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t116 :=
  t115 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t116.

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
  Start of ::
 ***********************)

Definition cons_ (T: Type) (thiss: List T) (t8: T) : List T :=
Cons_construct T t8 thiss.

Fail Next Obligation.

Hint Unfold cons_: definitions.

(***********************
  End of ::
 ***********************)


(***********************
  Start of groupBy
 ***********************)


Definition groupBy_rt_type (T: Type) (R: Type) (thiss13: List T) (f3: T -> R) : Type :=
map_type R (Option (List T)).

Fail Next Obligation.

Hint Unfold groupBy_rt_type.


Equations (noind) groupBy (T: Type) (R: Type) (thiss13: List T) (f3: T -> R) : groupBy_rt_type T R thiss13 f3 := 
	groupBy T R thiss13 f3 by rec ignore_termination lt :=
	groupBy T R thiss13 f3 := match thiss13 with
	| Nil_construct _ => magic (map_type R (Option (List T)))
	| Cons_construct _ h7 t117 => 
			let key := (f3 h7) in (let rest := (groupBy T R t117 f3) in (let prev := (ifthenelse (negb (propInBool ((magic (Option (List T)) = None_construct (List T))))) (List T)
				(fun _ => let assertion: (isSome _ (magic (Option (List T))) = true) := (_) in (v (List T) (let assertion1: (isSome _ (magic (Option (List T))) = true) := (_) in (magic (Option (List T))))) )
				(fun _ => Nil_construct T )) in (magic (map_type R (Option (List T))))))
	end.

Hint Unfold groupBy_comp_proj.

Solve Obligations with (repeat t116).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A9 := match goal with 
	| [ H169: context[groupBy ?T ?R ?thiss13 ?f3] |- _ ] => 
			poseNew (Mark (T,R,thiss13,f3) "unfolding groupBy_equation")
	| [  |- context[groupBy ?T ?R ?thiss13 ?f3] ] => 
			poseNew (Mark (T,R,thiss13,f3) "unfolding groupBy_equation")
end.

Ltac rwrtTac_B9 := match goal with 
	| [ H169: context[groupBy ?T ?R ?thiss13 ?f3], H269: Marked (?T,?R,?thiss13,?f3) "unfolding groupBy_equation" |- _ ] => 
			poseNew (Mark (T,R,thiss13,f3) "unfolded groupBy_equation");
			add_equation (groupBy_equation_1 T R thiss13 f3)
	| [ H269: Marked (?T,?R,?thiss13,?f3) "unfolding groupBy_equation" |- context[groupBy ?T ?R ?thiss13 ?f3] ] => 
			poseNew (Mark (T,R,thiss13,f3) "unfolded groupBy_equation");
			add_equation (groupBy_equation_1 T R thiss13 f3)
end.

Ltac rwrtTac9 := idtac; repeat rwrtTac_A9; repeat rwrtTac_B9.

Ltac t118 :=
  t_base ||
  List_tactic14 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t119 :=
  t118 ||
  rwrtTac9 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t119.

(***********************
  End of groupBy
 ***********************)
