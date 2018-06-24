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

Ltac t504 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t505 :=
  t504 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t505.


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

Lemma None_exists: (forall T: Type, forall self408: Option T, ((true = isNone T self408)) <-> (((None_construct T = self408)))). 
Proof.
	repeat t505 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self409: Option T, ((true = isSome T self409)) <-> ((exists tmp153: T, (Some_construct T tmp153 = self409)))). 
Proof.
	repeat t505 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic51 := match goal with 
	| [ H204: (true = isNone ?T ?self410) |- _ ] => 
			poseNew (Mark (T,self410) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H204)
	| [ H204: (isNone ?T ?self410 = true) |- _ ] => 
			poseNew (Mark (T,self410) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H204))
	| [ H205: (true = isSome ?T ?self411) |- _ ] => 
			poseNew (Mark (T,self411) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H205)
	| [ H205: (isSome ?T ?self411 = true) |- _ ] => 
			poseNew (Mark (T,self411) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H205))
	| _ => idtac
end.

Ltac t506 :=
  t_base ||
  Option_tactic51 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t507 :=
  t506 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t507.


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

Lemma Cons_exists: (forall T: Type, forall self412: List T, ((true = isCons T self412)) <-> ((exists tmp155: List T, exists tmp154: T, (Cons_construct T tmp154 tmp155 = self412)))). 
Proof.
	repeat t507 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self413: List T, ((true = isNil T self413)) <-> (((Nil_construct T = self413)))). 
Proof.
	repeat t507 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic51 := match goal with 
	| [ H206: (true = isCons ?T ?self414) |- _ ] => 
			poseNew (Mark (T,self414) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H206)
	| [ H206: (isCons ?T ?self414 = true) |- _ ] => 
			poseNew (Mark (T,self414) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H206))
	| [ H207: (true = isNil ?T ?self415) |- _ ] => 
			poseNew (Mark (T,self415) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H207)
	| [ H207: (isNil ?T ?self415 = true) |- _ ] => 
			poseNew (Mark (T,self415) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H207))
	| _ => Option_tactic51
end.

Ltac t508 :=
  t_base ||
  List_tactic51 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t509 :=
  t508 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t509.

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
  Start of content
 ***********************)

Obligation Tactic:=idtac.
Definition content_rt22_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt22_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt22_type T thiss1 := 
	content T thiss1 by rec ignore_termination lt :=
	content T thiss1 := match thiss1 with
	| Nil_construct _ => @set_empty T
	| Cons_construct _ h1 t15 => 
			set_union (set_union (@set_empty T) (set_singleton h1)) (content T t15)
	end.

Hint Unfold content_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A87 := match goal with 
	| [ H1295: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B87 := match goal with 
	| [ H1295: context[content ?T ?thiss1], H2295: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2295: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac87 := idtac; repeat rwrtTac_A87; repeat rwrtTac_B87.

Ltac t510 :=
  t_base ||
  List_tactic51 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t511 :=
  t510 ||
  rwrtTac87 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t511.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt20_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt20_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt20_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A88 := match goal with 
	| [ H1296: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B88 := match goal with 
	| [ H1296: context[size ?T ?thiss30], H2296: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2296: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac88 := rwrtTac87; repeat rwrtTac_A88; repeat rwrtTac_B88.

Ltac t512 :=
  t_base ||
  List_tactic51 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t513 :=
  t512 ||
  rwrtTac88 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t513.

(***********************
  End of size
 ***********************)

(***********************
  Start of ++
 ***********************)

Obligation Tactic:=idtac.
Definition plus_plus__rt5_type (T: Type) (thiss32: List T) (that1: List T) : Type :=
{res3: List T | (ifthenelse
	(ifthenelse (set_equality (content T res3) (set_union (content T thiss32) (content T that1))) bool
		(fun _ => Zeq_bool (proj1_sig (size T res3)) (Z.add (proj1_sig (size T thiss32)) (proj1_sig (size T that1))) )
		(fun _ => false ))
	bool
	(fun _ => ifthenelse (negb (propInBool ((that1 = Nil_construct T)))) bool
		(fun _ => true )
		(fun _ => propInBool ((res3 = thiss32)) ) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold plus_plus__rt5_type.


Equations (noind) plus_plus_ (T: Type) (thiss32: List T) (that1: List T) : plus_plus__rt5_type T thiss32 that1 := 
	plus_plus_ T thiss32 that1 by rec ignore_termination lt :=
	plus_plus_ T thiss32 that1 := match thiss32 with
	| Nil_construct _ => that1
	| Cons_construct _ x2 xs => Cons_construct T x2 (proj1_sig (plus_plus_ T xs that1))
	end.

Hint Unfold plus_plus__comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A89 := match goal with 
	| [ H1297: context[plus_plus_ ?T ?thiss32 ?that1] |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
	| [  |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
end.

Ltac rwrtTac_B89 := match goal with 
	| [ H1297: context[plus_plus_ ?T ?thiss32 ?that1], H2297: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
	| [ H2297: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
end.

Ltac rwrtTac89 := rwrtTac88; repeat rwrtTac_A89; repeat rwrtTac_B89.

Ltac t514 :=
  t_base ||
  List_tactic51 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t515 :=
  t514 ||
  rwrtTac89 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t515.

(***********************
  End of ++
 ***********************)

(***********************
  Start of flatten
 ***********************)

Obligation Tactic:=idtac.
Definition flatten_rt1_type (T: Type) (ls: List (List T)) : Type :=
List T.

Fail Next Obligation.

Hint Unfold flatten_rt1_type.


Equations (noind) flatten (T: Type) (ls: List (List T)) : flatten_rt1_type T ls := 
	flatten T ls by rec ignore_termination lt :=
	flatten T ls := match ls with
	| Cons_construct _ h18 t427 => proj1_sig (plus_plus_ T h18 (flatten T t427))
	| Nil_construct _ => Nil_construct T
	end.

Hint Unfold flatten_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A90 := match goal with 
	| [ H1298: context[flatten ?T ?ls] |- _ ] => 
			poseNew (Mark (T,ls) "unfolding flatten_equation")
	| [  |- context[flatten ?T ?ls] ] => 
			poseNew (Mark (T,ls) "unfolding flatten_equation")
end.

Ltac rwrtTac_B90 := match goal with 
	| [ H1298: context[flatten ?T ?ls], H2298: Marked (?T,?ls) "unfolding flatten_equation" |- _ ] => 
			poseNew (Mark (T,ls) "unfolded flatten_equation");
			add_equation (flatten_equation_1 T ls)
	| [ H2298: Marked (?T,?ls) "unfolding flatten_equation" |- context[flatten ?T ?ls] ] => 
			poseNew (Mark (T,ls) "unfolded flatten_equation");
			add_equation (flatten_equation_1 T ls)
end.

Ltac rwrtTac90 := rwrtTac89; repeat rwrtTac_A90; repeat rwrtTac_B90.

Ltac t516 :=
  t_base ||
  List_tactic51 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t517 :=
  t516 ||
  rwrtTac90 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t517.

(***********************
  End of flatten
 ***********************)

(***********************
  Start of map
 ***********************)

Obligation Tactic:=idtac.
Definition map1_rt1_type (T: Type) (R: Type) (thiss48: List T) (f7: T -> R) : Type :=
{x___9: List R | (Zeq_bool (proj1_sig (size R x___9)) (proj1_sig (size T thiss48)) = true)}.

Fail Next Obligation.

Hint Unfold map1_rt1_type.


Equations (noind) map1 (T: Type) (R: Type) (thiss48: List T) (f7: T -> R) : map1_rt1_type T R thiss48 f7 := 
	map1 T R thiss48 f7 by rec ignore_termination lt :=
	map1 T R thiss48 f7 := match thiss48 with
	| Nil_construct _ => Nil_construct R
	| Cons_construct _ h20 t501 => 
			let x___8 := (f7 h20) in (cons_ R (proj1_sig (map1 T R t501 f7)) x___8)
	end.

Hint Unfold map1_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A91 := match goal with 
	| [ H1299: context[map1 ?T ?R ?thiss48 ?f7] |- _ ] => 
			poseNew (Mark (T,R,thiss48,f7) "unfolding map1_equation")
	| [  |- context[map1 ?T ?R ?thiss48 ?f7] ] => 
			poseNew (Mark (T,R,thiss48,f7) "unfolding map1_equation")
end.

Ltac rwrtTac_B91 := match goal with 
	| [ H1299: context[map1 ?T ?R ?thiss48 ?f7], H2299: Marked (?T,?R,?thiss48,?f7) "unfolding map1_equation" |- _ ] => 
			poseNew (Mark (T,R,thiss48,f7) "unfolded map1_equation");
			add_equation (map1_equation_1 T R thiss48 f7)
	| [ H2299: Marked (?T,?R,?thiss48,?f7) "unfolding map1_equation" |- context[map1 ?T ?R ?thiss48 ?f7] ] => 
			poseNew (Mark (T,R,thiss48,f7) "unfolded map1_equation");
			add_equation (map1_equation_1 T R thiss48 f7)
end.

Ltac rwrtTac91 := rwrtTac90; repeat rwrtTac_A91; repeat rwrtTac_B91.

Ltac t518 :=
  t_base ||
  List_tactic51 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t519 :=
  t518 ||
  rwrtTac91 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t519.

(***********************
  End of map
 ***********************)


(***********************
  Start of flatMap
 ***********************)

Definition flatMap1 (T: Type) (R: Type) (thiss49: List T) (f8: T -> (List R)) : List R :=
flatten R (proj1_sig (map1 T (List R) thiss49 f8)).

Fail Next Obligation.

Hint Unfold flatMap1: definitions.

(***********************
  End of flatMap
 ***********************)
