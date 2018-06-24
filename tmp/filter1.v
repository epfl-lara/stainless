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

Ltac t370 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t371 :=
  t370 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t371.


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

Lemma None_exists: (forall T: Type, forall self328: Option T, ((true = isNone T self328)) <-> (((None_construct T = self328)))). 
Proof.
	repeat t371 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self329: Option T, ((true = isSome T self329)) <-> ((exists tmp123: T, (Some_construct T tmp123 = self329)))). 
Proof.
	repeat t371 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic41 := match goal with 
	| [ H164: (true = isNone ?T ?self330) |- _ ] => 
			poseNew (Mark (T,self330) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H164)
	| [ H164: (isNone ?T ?self330 = true) |- _ ] => 
			poseNew (Mark (T,self330) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H164))
	| [ H165: (true = isSome ?T ?self331) |- _ ] => 
			poseNew (Mark (T,self331) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H165)
	| [ H165: (isSome ?T ?self331 = true) |- _ ] => 
			poseNew (Mark (T,self331) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H165))
	| _ => idtac
end.

Ltac t372 :=
  t_base ||
  Option_tactic41 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t373 :=
  t372 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t373.


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

Lemma Cons_exists: (forall T: Type, forall self332: List T, ((true = isCons T self332)) <-> ((exists tmp125: List T, exists tmp124: T, (Cons_construct T tmp124 tmp125 = self332)))). 
Proof.
	repeat t373 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self333: List T, ((true = isNil T self333)) <-> (((Nil_construct T = self333)))). 
Proof.
	repeat t373 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic41 := match goal with 
	| [ H166: (true = isCons ?T ?self334) |- _ ] => 
			poseNew (Mark (T,self334) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H166)
	| [ H166: (isCons ?T ?self334 = true) |- _ ] => 
			poseNew (Mark (T,self334) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H166))
	| [ H167: (true = isNil ?T ?self335) |- _ ] => 
			poseNew (Mark (T,self335) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H167)
	| [ H167: (isNil ?T ?self335 = true) |- _ ] => 
			poseNew (Mark (T,self335) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H167))
	| _ => Option_tactic41
end.

Ltac t374 :=
  t_base ||
  List_tactic41 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t375 :=
  t374 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t375.

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
  Start of content
 ***********************)

Obligation Tactic:=idtac.
Definition content_rt14_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt14_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt14_type T thiss1 := 
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

Ltac rwrtTac_A52 := match goal with 
	| [ H1220: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B52 := match goal with 
	| [ H1220: context[content ?T ?thiss1], H2220: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2220: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac52 := idtac; repeat rwrtTac_A52; repeat rwrtTac_B52.

Ltac t376 :=
  t_base ||
  List_tactic41 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t377 :=
  t376 ||
  rwrtTac52 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t377.

(***********************
  End of content
 ***********************)

(***********************
  Start of forall
 ***********************)

Obligation Tactic:=idtac.
Definition _forall_rt3_type (T: Type) (thiss8: List T) (p2: T -> bool) : Type :=
bool.

Fail Next Obligation.

Hint Unfold _forall_rt3_type.


Equations (noind) _forall (T: Type) (thiss8: List T) (p2: T -> bool) : _forall_rt3_type T thiss8 p2 := 
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

Ltac rwrtTac_A53 := match goal with 
	| [ H1221: context[_forall ?T ?thiss8 ?p2] |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
	| [  |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
end.

Ltac rwrtTac_B53 := match goal with 
	| [ H1221: context[_forall ?T ?thiss8 ?p2], H2221: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
	| [ H2221: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
end.

Ltac rwrtTac53 := rwrtTac52; repeat rwrtTac_A53; repeat rwrtTac_B53.

Ltac t378 :=
  t_base ||
  List_tactic41 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t379 :=
  t378 ||
  rwrtTac53 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t379.

(***********************
  End of forall
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt10_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt10_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt10_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A54 := match goal with 
	| [ H1222: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B54 := match goal with 
	| [ H1222: context[size ?T ?thiss30], H2222: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2222: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac54 := rwrtTac53; repeat rwrtTac_A54; repeat rwrtTac_B54.

Ltac t380 :=
  t_base ||
  List_tactic41 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t381 :=
  t380 ||
  rwrtTac54 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t381.

(***********************
  End of size
 ***********************)


(***********************
  Start of filter
 ***********************)


Definition filter1_rt_type (T: Type) (thiss40: List T) (p8: T -> bool) : Type :=
{res10: List T | (ifthenelse
	(ifthenelse (Z.leb (proj1_sig (size T res10)) (proj1_sig (size T thiss40))) bool
		(fun _ => set_subset (content T res10) (content T thiss40) )
		(fun _ => false ))
	bool
	(fun _ => _forall T res10 p8 )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold filter1_rt_type.


Equations (noind) filter1 (T: Type) (thiss40: List T) (p8: T -> bool) : filter1_rt_type T thiss40 p8 := 
	filter1 T thiss40 p8 by rec ignore_termination lt :=
	filter1 T thiss40 p8 := ifthenelse (isNil _ thiss40) (List T)
		(fun _ => Nil_construct T )
		(fun _ => ifthenelse
			(ifthenelse (isCons _ thiss40) bool
				(fun _ => p8 (h T thiss40) )
				(fun _ => false ))
			(List T)
			(fun _ => Cons_construct T (h T thiss40) (proj1_sig (filter1 T (t7 T thiss40) p8)) )
			(fun _ => ifthenelse (isCons _ thiss40) (List T)
				(fun _ => proj1_sig (filter1 T (t7 T thiss40) p8) )
				(fun _ => let contradiction: False := _ in match contradiction with end ) ) ).

Hint Unfold filter1_comp_proj.

Solve Obligations with (repeat t381).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A55 := match goal with 
	| [ H1223: context[filter1 ?T ?thiss40 ?p8] |- _ ] => 
			poseNew (Mark (T,thiss40,p8) "unfolding filter1_equation")
	| [  |- context[filter1 ?T ?thiss40 ?p8] ] => 
			poseNew (Mark (T,thiss40,p8) "unfolding filter1_equation")
end.

Ltac rwrtTac_B55 := match goal with 
	| [ H1223: context[filter1 ?T ?thiss40 ?p8], H2223: Marked (?T,?thiss40,?p8) "unfolding filter1_equation" |- _ ] => 
			poseNew (Mark (T,thiss40,p8) "unfolded filter1_equation");
			add_equation (filter1_equation_1 T thiss40 p8)
	| [ H2223: Marked (?T,?thiss40,?p8) "unfolding filter1_equation" |- context[filter1 ?T ?thiss40 ?p8] ] => 
			poseNew (Mark (T,thiss40,p8) "unfolded filter1_equation");
			add_equation (filter1_equation_1 T thiss40 p8)
end.

Ltac rwrtTac55 := rwrtTac54; repeat rwrtTac_A55; repeat rwrtTac_B55.

Ltac t382 :=
  t_base ||
  List_tactic41 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t383 :=
  t382 ||
  rwrtTac55 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t383.

(***********************
  End of filter
 ***********************)
