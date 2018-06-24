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

Ltac t493 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t494 :=
  t493 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t494.


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

Lemma None_exists: (forall T: Type, forall self400: Option T, ((true = isNone T self400)) <-> (((None_construct T = self400)))). 
Proof.
	repeat t494 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self401: Option T, ((true = isSome T self401)) <-> ((exists tmp150: T, (Some_construct T tmp150 = self401)))). 
Proof.
	repeat t494 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic50 := match goal with 
	| [ H200: (true = isNone ?T ?self402) |- _ ] => 
			poseNew (Mark (T,self402) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H200)
	| [ H200: (isNone ?T ?self402 = true) |- _ ] => 
			poseNew (Mark (T,self402) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H200))
	| [ H201: (true = isSome ?T ?self403) |- _ ] => 
			poseNew (Mark (T,self403) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H201)
	| [ H201: (isSome ?T ?self403 = true) |- _ ] => 
			poseNew (Mark (T,self403) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H201))
	| _ => idtac
end.

Ltac t495 :=
  t_base ||
  Option_tactic50 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t496 :=
  t495 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t496.


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

Lemma Cons_exists: (forall T: Type, forall self404: List T, ((true = isCons T self404)) <-> ((exists tmp152: List T, exists tmp151: T, (Cons_construct T tmp151 tmp152 = self404)))). 
Proof.
	repeat t496 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self405: List T, ((true = isNil T self405)) <-> (((Nil_construct T = self405)))). 
Proof.
	repeat t496 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic50 := match goal with 
	| [ H202: (true = isCons ?T ?self406) |- _ ] => 
			poseNew (Mark (T,self406) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H202)
	| [ H202: (isCons ?T ?self406 = true) |- _ ] => 
			poseNew (Mark (T,self406) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H202))
	| [ H203: (true = isNil ?T ?self407) |- _ ] => 
			poseNew (Mark (T,self407) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H203)
	| [ H203: (isNil ?T ?self407 = true) |- _ ] => 
			poseNew (Mark (T,self407) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H203))
	| _ => Option_tactic50
end.

Ltac t497 :=
  t_base ||
  List_tactic50 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t498 :=
  t497 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t498.

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
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt19_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt19_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt19_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A85 := match goal with 
	| [ H1289: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B85 := match goal with 
	| [ H1289: context[size ?T ?thiss30], H2289: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2289: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac85 := idtac; repeat rwrtTac_A85; repeat rwrtTac_B85.

Ltac t499 :=
  t_base ||
  List_tactic50 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t500 :=
  t499 ||
  rwrtTac85 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t500.

(***********************
  End of size
 ***********************)


(***********************
  Start of map
 ***********************)


Definition map1_rt_type (T: Type) (R: Type) (thiss48: List T) (f7: T -> R) : Type :=
{x___9: List R | (Zeq_bool (proj1_sig (size R x___9)) (proj1_sig (size T thiss48)) = true)}.

Fail Next Obligation.

Hint Unfold map1_rt_type.


Equations (noind) map1 (T: Type) (R: Type) (thiss48: List T) (f7: T -> R) : map1_rt_type T R thiss48 f7 := 
	map1 T R thiss48 f7 by rec ignore_termination lt :=
	map1 T R thiss48 f7 := match thiss48 with
	| Nil_construct _ => Nil_construct R
	| Cons_construct _ h20 t501 => 
			let x___8 := (f7 h20) in (cons_ R (proj1_sig (map1 T R t501 f7)) x___8)
	end.

Hint Unfold map1_comp_proj.

Solve Obligations with (repeat t500).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A86 := match goal with 
	| [ H1290: context[map1 ?T ?R ?thiss48 ?f7] |- _ ] => 
			poseNew (Mark (T,R,thiss48,f7) "unfolding map1_equation")
	| [  |- context[map1 ?T ?R ?thiss48 ?f7] ] => 
			poseNew (Mark (T,R,thiss48,f7) "unfolding map1_equation")
end.

Ltac rwrtTac_B86 := match goal with 
	| [ H1290: context[map1 ?T ?R ?thiss48 ?f7], H2290: Marked (?T,?R,?thiss48,?f7) "unfolding map1_equation" |- _ ] => 
			poseNew (Mark (T,R,thiss48,f7) "unfolded map1_equation");
			add_equation (map1_equation_1 T R thiss48 f7)
	| [ H2290: Marked (?T,?R,?thiss48,?f7) "unfolding map1_equation" |- context[map1 ?T ?R ?thiss48 ?f7] ] => 
			poseNew (Mark (T,R,thiss48,f7) "unfolded map1_equation");
			add_equation (map1_equation_1 T R thiss48 f7)
end.

Ltac rwrtTac86 := rwrtTac85; repeat rwrtTac_A86; repeat rwrtTac_B86.

Ltac t502 :=
  t_base ||
  List_tactic50 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t503 :=
  t502 ||
  rwrtTac86 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t503.

(***********************
  End of map
 ***********************)
