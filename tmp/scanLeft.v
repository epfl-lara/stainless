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

Ltac t222 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t223 :=
  t222 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t223.


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

Lemma None_exists: (forall T: Type, forall self232: Option T, ((true = isNone T self232)) <-> (((None_construct T = self232)))). 
Proof.
	repeat t223 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self233: Option T, ((true = isSome T self233)) <-> ((exists tmp87: T, (Some_construct T tmp87 = self233)))). 
Proof.
	repeat t223 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic29 := match goal with 
	| [ H116: (true = isNone ?T ?self234) |- _ ] => 
			poseNew (Mark (T,self234) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H116)
	| [ H116: (isNone ?T ?self234 = true) |- _ ] => 
			poseNew (Mark (T,self234) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H116))
	| [ H117: (true = isSome ?T ?self235) |- _ ] => 
			poseNew (Mark (T,self235) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H117)
	| [ H117: (isSome ?T ?self235 = true) |- _ ] => 
			poseNew (Mark (T,self235) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H117))
	| _ => idtac
end.

Ltac t224 :=
  t_base ||
  Option_tactic29 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t225 :=
  t224 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t225.


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

Lemma Cons_exists: (forall T: Type, forall self236: List T, ((true = isCons T self236)) <-> ((exists tmp89: List T, exists tmp88: T, (Cons_construct T tmp88 tmp89 = self236)))). 
Proof.
	repeat t225 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self237: List T, ((true = isNil T self237)) <-> (((Nil_construct T = self237)))). 
Proof.
	repeat t225 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic29 := match goal with 
	| [ H118: (true = isCons ?T ?self238) |- _ ] => 
			poseNew (Mark (T,self238) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H118)
	| [ H118: (isCons ?T ?self238 = true) |- _ ] => 
			poseNew (Mark (T,self238) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H118))
	| [ H119: (true = isNil ?T ?self239) |- _ ] => 
			poseNew (Mark (T,self239) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H119)
	| [ H119: (isNil ?T ?self239 = true) |- _ ] => 
			poseNew (Mark (T,self239) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H119))
	| _ => Option_tactic29
end.

Ltac t226 :=
  t_base ||
  List_tactic29 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t227 :=
  t226 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t227.

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
  Start of scanLeft
 ***********************)


Definition scanLeft_rt_type (T: Type) (R: Type) (thiss28: List T) (z2: R) (f5: R -> (T -> R)) : Type :=
{x___12: List R | (negb (isEmpty R x___12) = true)}.

Fail Next Obligation.

Hint Unfold scanLeft_rt_type.


Equations (noind) scanLeft (T: Type) (R: Type) (thiss28: List T) (z2: R) (f5: R -> (T -> R)) : scanLeft_rt_type T R thiss28 z2 f5 := 
	scanLeft T R thiss28 z2 f5 by rec ignore_termination lt :=
	scanLeft T R thiss28 z2 f5 := match thiss28 with
	| Nil_construct _ => cons_ R (Nil_construct R) z2
	| Cons_construct _ h10 t228 => 
			cons_ R (proj1_sig (scanLeft T R t228 (f5 z2 h10) f5)) z2
	end.

Hint Unfold scanLeft_comp_proj.

Solve Obligations with (repeat t227).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A18 := match goal with 
	| [ H1138: context[scanLeft ?T ?R ?thiss28 ?z2 ?f5] |- _ ] => 
			poseNew (Mark (T,R,thiss28,z2,f5) "unfolding scanLeft_equation")
	| [  |- context[scanLeft ?T ?R ?thiss28 ?z2 ?f5] ] => 
			poseNew (Mark (T,R,thiss28,z2,f5) "unfolding scanLeft_equation")
end.

Ltac rwrtTac_B18 := match goal with 
	| [ H1138: context[scanLeft ?T ?R ?thiss28 ?z2 ?f5], H2138: Marked (?T,?R,?thiss28,?z2,?f5) "unfolding scanLeft_equation" |- _ ] => 
			poseNew (Mark (T,R,thiss28,z2,f5) "unfolded scanLeft_equation");
			add_equation (scanLeft_equation_1 T R thiss28 z2 f5)
	| [ H2138: Marked (?T,?R,?thiss28,?z2,?f5) "unfolding scanLeft_equation" |- context[scanLeft ?T ?R ?thiss28 ?z2 ?f5] ] => 
			poseNew (Mark (T,R,thiss28,z2,f5) "unfolded scanLeft_equation");
			add_equation (scanLeft_equation_1 T R thiss28 z2 f5)
end.

Ltac rwrtTac18 := idtac; repeat rwrtTac_A18; repeat rwrtTac_B18.

Ltac t229 :=
  t_base ||
  List_tactic29 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t230 :=
  t229 ||
  rwrtTac18 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t230.

(***********************
  End of scanLeft
 ***********************)
