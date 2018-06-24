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

Ltac t759 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t760 :=
  t759 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t760.


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

Lemma None_exists: (forall T: Type, forall self568: Option T, ((true = isNone T self568)) <-> (((None_construct T = self568)))). 
Proof.
	repeat t760 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self569: Option T, ((true = isSome T self569)) <-> ((exists tmp213: T, (Some_construct T tmp213 = self569)))). 
Proof.
	repeat t760 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic71 := match goal with 
	| [ H284: (true = isNone ?T ?self570) |- _ ] => 
			poseNew (Mark (T,self570) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H284)
	| [ H284: (isNone ?T ?self570 = true) |- _ ] => 
			poseNew (Mark (T,self570) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H284))
	| [ H285: (true = isSome ?T ?self571) |- _ ] => 
			poseNew (Mark (T,self571) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H285)
	| [ H285: (isSome ?T ?self571 = true) |- _ ] => 
			poseNew (Mark (T,self571) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H285))
	| _ => idtac
end.

Ltac t761 :=
  t_base ||
  Option_tactic71 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t762 :=
  t761 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t762.


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

Lemma Cons_exists: (forall T: Type, forall self572: List T, ((true = isCons T self572)) <-> ((exists tmp215: List T, exists tmp214: T, (Cons_construct T tmp214 tmp215 = self572)))). 
Proof.
	repeat t762 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self573: List T, ((true = isNil T self573)) <-> (((Nil_construct T = self573)))). 
Proof.
	repeat t762 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic71 := match goal with 
	| [ H286: (true = isCons ?T ?self574) |- _ ] => 
			poseNew (Mark (T,self574) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H286)
	| [ H286: (isCons ?T ?self574 = true) |- _ ] => 
			poseNew (Mark (T,self574) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H286))
	| [ H287: (true = isNil ?T ?self575) |- _ ] => 
			poseNew (Mark (T,self575) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H287)
	| [ H287: (isNil ?T ?self575 = true) |- _ ] => 
			poseNew (Mark (T,self575) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H287))
	| _ => Option_tactic71
end.

Ltac t763 :=
  t_base ||
  List_tactic71 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t764 :=
  t763 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t764.

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
  Start of foldLeft
 ***********************)

Obligation Tactic:=idtac.
Definition foldLeft_rt1_type (T: Type) (R: Type) (thiss6: List T) (z: R) (f1: R -> (T -> R)) : Type :=
R.

Fail Next Obligation.

Hint Unfold foldLeft_rt1_type.


Equations (noind) foldLeft (T: Type) (R: Type) (thiss6: List T) (z: R) (f1: R -> (T -> R)) : foldLeft_rt1_type T R thiss6 z f1 := 
	foldLeft T R thiss6 z f1 by rec ignore_termination lt :=
	foldLeft T R thiss6 z f1 := match thiss6 with
	| Nil_construct _ => z
	| Cons_construct _ h4 t64 => foldLeft T R t64 (f1 z h4) f1
	end.

Hint Unfold foldLeft_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A152 := match goal with 
	| [ H1440: context[foldLeft ?T ?R ?thiss6 ?z ?f1] |- _ ] => 
			poseNew (Mark (T,R,thiss6,z,f1) "unfolding foldLeft_equation")
	| [  |- context[foldLeft ?T ?R ?thiss6 ?z ?f1] ] => 
			poseNew (Mark (T,R,thiss6,z,f1) "unfolding foldLeft_equation")
end.

Ltac rwrtTac_B152 := match goal with 
	| [ H1440: context[foldLeft ?T ?R ?thiss6 ?z ?f1], H2440: Marked (?T,?R,?thiss6,?z,?f1) "unfolding foldLeft_equation" |- _ ] => 
			poseNew (Mark (T,R,thiss6,z,f1) "unfolded foldLeft_equation");
			add_equation (foldLeft_equation_1 T R thiss6 z f1)
	| [ H2440: Marked (?T,?R,?thiss6,?z,?f1) "unfolding foldLeft_equation" |- context[foldLeft ?T ?R ?thiss6 ?z ?f1] ] => 
			poseNew (Mark (T,R,thiss6,z,f1) "unfolded foldLeft_equation");
			add_equation (foldLeft_equation_1 T R thiss6 z f1)
end.

Ltac rwrtTac152 := idtac; repeat rwrtTac_A152; repeat rwrtTac_B152.

Ltac t765 :=
  t_base ||
  List_tactic71 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t766 :=
  t765 ||
  rwrtTac152 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t766.

(***********************
  End of foldLeft
 ***********************)


(***********************
  Start of toSet
 ***********************)

Definition toSet1 (T: Type) (thiss68: List T) : set (T) :=
foldLeft T (set (T)) thiss68 (@set_empty T) (fun x0___1 => fun x1___1 => set_union x0___1 (set_union (@set_empty T) (set_singleton x1___1))  ).

Fail Next Obligation.

Hint Unfold toSet1: definitions.

(***********************
  End of toSet
 ***********************)
