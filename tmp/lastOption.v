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

Ltac t213 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t214 :=
  t213 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t214.


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

Lemma None_exists: (forall T: Type, forall self224: Option T, ((true = isNone T self224)) <-> (((None_construct T = self224)))). 
Proof.
	repeat t214 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self225: Option T, ((true = isSome T self225)) <-> ((exists tmp84: T, (Some_construct T tmp84 = self225)))). 
Proof.
	repeat t214 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic28 := match goal with 
	| [ H112: (true = isNone ?T ?self226) |- _ ] => 
			poseNew (Mark (T,self226) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H112)
	| [ H112: (isNone ?T ?self226 = true) |- _ ] => 
			poseNew (Mark (T,self226) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H112))
	| [ H113: (true = isSome ?T ?self227) |- _ ] => 
			poseNew (Mark (T,self227) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H113)
	| [ H113: (isSome ?T ?self227 = true) |- _ ] => 
			poseNew (Mark (T,self227) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H113))
	| _ => idtac
end.

Ltac t215 :=
  t_base ||
  Option_tactic28 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t216 :=
  t215 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t216.


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

Lemma Cons_exists: (forall T: Type, forall self228: List T, ((true = isCons T self228)) <-> ((exists tmp86: List T, exists tmp85: T, (Cons_construct T tmp85 tmp86 = self228)))). 
Proof.
	repeat t216 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self229: List T, ((true = isNil T self229)) <-> (((Nil_construct T = self229)))). 
Proof.
	repeat t216 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic28 := match goal with 
	| [ H114: (true = isCons ?T ?self230) |- _ ] => 
			poseNew (Mark (T,self230) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H114)
	| [ H114: (isCons ?T ?self230 = true) |- _ ] => 
			poseNew (Mark (T,self230) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H114))
	| [ H115: (true = isNil ?T ?self231) |- _ ] => 
			poseNew (Mark (T,self231) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H115)
	| [ H115: (isNil ?T ?self231 = true) |- _ ] => 
			poseNew (Mark (T,self231) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H115))
	| _ => Option_tactic28
end.

Ltac t217 :=
  t_base ||
  List_tactic28 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t218 :=
  t217 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t218.

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


(***********************
  Start of lastOption
 ***********************)


Definition lastOption_rt_type (T: Type) (thiss27: List T) : Type :=
{x___4: Option T | (negb (Bool.eqb (isDefined T x___4) (isEmpty T thiss27)) = true)}.

Fail Next Obligation.

Hint Unfold lastOption_rt_type.


Equations (noind) lastOption (T: Type) (thiss27: List T) : lastOption_rt_type T thiss27 := 
	lastOption T thiss27 by rec ignore_termination lt :=
	lastOption T thiss27 := match thiss27 with
	| Cons_construct _ h9 t219 => 
			proj1_sig (orElse T (proj1_sig (lastOption T t219)) (Some_construct T h9))
	| Nil_construct _ => None_construct T
	end.

Hint Unfold lastOption_comp_proj.

Solve Obligations with (repeat t218).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A17 := match goal with 
	| [ H1133: context[lastOption ?T ?thiss27] |- _ ] => 
			poseNew (Mark (T,thiss27) "unfolding lastOption_equation")
	| [  |- context[lastOption ?T ?thiss27] ] => 
			poseNew (Mark (T,thiss27) "unfolding lastOption_equation")
end.

Ltac rwrtTac_B17 := match goal with 
	| [ H1133: context[lastOption ?T ?thiss27], H2133: Marked (?T,?thiss27) "unfolding lastOption_equation" |- _ ] => 
			poseNew (Mark (T,thiss27) "unfolded lastOption_equation");
			add_equation (lastOption_equation_1 T thiss27)
	| [ H2133: Marked (?T,?thiss27) "unfolding lastOption_equation" |- context[lastOption ?T ?thiss27] ] => 
			poseNew (Mark (T,thiss27) "unfolded lastOption_equation");
			add_equation (lastOption_equation_1 T thiss27)
end.

Ltac rwrtTac17 := idtac; repeat rwrtTac_A17; repeat rwrtTac_B17.

Ltac t220 :=
  t_base ||
  List_tactic28 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t221 :=
  t220 ||
  rwrtTac17 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t221.

(***********************
  End of lastOption
 ***********************)
