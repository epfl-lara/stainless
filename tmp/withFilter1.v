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

Ltac t798 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t799 :=
  t798 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t799.


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

Lemma None_exists: (forall T: Type, forall self600: Option T, ((true = isNone T self600)) <-> (((None_construct T = self600)))). 
Proof.
	repeat t799 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self601: Option T, ((true = isSome T self601)) <-> ((exists tmp225: T, (Some_construct T tmp225 = self601)))). 
Proof.
	repeat t799 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic75 := match goal with 
	| [ H300: (true = isNone ?T ?self602) |- _ ] => 
			poseNew (Mark (T,self602) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H300)
	| [ H300: (isNone ?T ?self602 = true) |- _ ] => 
			poseNew (Mark (T,self602) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H300))
	| [ H301: (true = isSome ?T ?self603) |- _ ] => 
			poseNew (Mark (T,self603) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H301)
	| [ H301: (isSome ?T ?self603 = true) |- _ ] => 
			poseNew (Mark (T,self603) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H301))
	| _ => idtac
end.

Ltac t800 :=
  t_base ||
  Option_tactic75 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t801 :=
  t800 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t801.


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

Lemma Cons_exists: (forall T: Type, forall self604: List T, ((true = isCons T self604)) <-> ((exists tmp227: List T, exists tmp226: T, (Cons_construct T tmp226 tmp227 = self604)))). 
Proof.
	repeat t801 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self605: List T, ((true = isNil T self605)) <-> (((Nil_construct T = self605)))). 
Proof.
	repeat t801 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic75 := match goal with 
	| [ H302: (true = isCons ?T ?self606) |- _ ] => 
			poseNew (Mark (T,self606) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H302)
	| [ H302: (isCons ?T ?self606 = true) |- _ ] => 
			poseNew (Mark (T,self606) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H302))
	| [ H303: (true = isNil ?T ?self607) |- _ ] => 
			poseNew (Mark (T,self607) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H303)
	| [ H303: (isNil ?T ?self607 = true) |- _ ] => 
			poseNew (Mark (T,self607) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H303))
	| _ => Option_tactic75
end.

Ltac t802 :=
  t_base ||
  List_tactic75 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t803 :=
  t802 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t803.

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
Definition content_rt38_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt38_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt38_type T thiss1 := 
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

Ltac rwrtTac_A159 := match goal with 
	| [ H1463: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B159 := match goal with 
	| [ H1463: context[content ?T ?thiss1], H2463: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2463: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac159 := idtac; repeat rwrtTac_A159; repeat rwrtTac_B159.

Ltac t804 :=
  t_base ||
  List_tactic75 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t805 :=
  t804 ||
  rwrtTac159 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t805.

(***********************
  End of content
 ***********************)

(***********************
  Start of forall
 ***********************)

Obligation Tactic:=idtac.
Definition _forall_rt8_type (T: Type) (thiss8: List T) (p2: T -> bool) : Type :=
bool.

Fail Next Obligation.

Hint Unfold _forall_rt8_type.


Equations (noind) _forall (T: Type) (thiss8: List T) (p2: T -> bool) : _forall_rt8_type T thiss8 p2 := 
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

Ltac rwrtTac_A160 := match goal with 
	| [ H1464: context[_forall ?T ?thiss8 ?p2] |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
	| [  |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
end.

Ltac rwrtTac_B160 := match goal with 
	| [ H1464: context[_forall ?T ?thiss8 ?p2], H2464: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
	| [ H2464: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
end.

Ltac rwrtTac160 := rwrtTac159; repeat rwrtTac_A160; repeat rwrtTac_B160.

Ltac t806 :=
  t_base ||
  List_tactic75 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t807 :=
  t806 ||
  rwrtTac160 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t807.

(***********************
  End of forall
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt36_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt36_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt36_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A161 := match goal with 
	| [ H1465: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B161 := match goal with 
	| [ H1465: context[size ?T ?thiss30], H2465: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2465: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac161 := rwrtTac160; repeat rwrtTac_A161; repeat rwrtTac_B161.

Ltac t808 :=
  t_base ||
  List_tactic75 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t809 :=
  t808 ||
  rwrtTac161 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t809.

(***********************
  End of size
 ***********************)

(***********************
  Start of filter
 ***********************)

Obligation Tactic:=idtac.
Definition filter1_rt4_type (T: Type) (thiss40: List T) (p8: T -> bool) : Type :=
{res10: List T | (ifthenelse
	(ifthenelse (Z.leb (proj1_sig (size T res10)) (proj1_sig (size T thiss40))) bool
		(fun _ => set_subset (content T res10) (content T thiss40) )
		(fun _ => false ))
	bool
	(fun _ => _forall T res10 p8 )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold filter1_rt4_type.


Equations (noind) filter1 (T: Type) (thiss40: List T) (p8: T -> bool) : filter1_rt4_type T thiss40 p8 := 
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

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A162 := match goal with 
	| [ H1466: context[filter1 ?T ?thiss40 ?p8] |- _ ] => 
			poseNew (Mark (T,thiss40,p8) "unfolding filter1_equation")
	| [  |- context[filter1 ?T ?thiss40 ?p8] ] => 
			poseNew (Mark (T,thiss40,p8) "unfolding filter1_equation")
end.

Ltac rwrtTac_B162 := match goal with 
	| [ H1466: context[filter1 ?T ?thiss40 ?p8], H2466: Marked (?T,?thiss40,?p8) "unfolding filter1_equation" |- _ ] => 
			poseNew (Mark (T,thiss40,p8) "unfolded filter1_equation");
			add_equation (filter1_equation_1 T thiss40 p8)
	| [ H2466: Marked (?T,?thiss40,?p8) "unfolding filter1_equation" |- context[filter1 ?T ?thiss40 ?p8] ] => 
			poseNew (Mark (T,thiss40,p8) "unfolded filter1_equation");
			add_equation (filter1_equation_1 T thiss40 p8)
end.

Ltac rwrtTac162 := rwrtTac161; repeat rwrtTac_A162; repeat rwrtTac_B162.

Ltac t810 :=
  t_base ||
  List_tactic75 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t811 :=
  t810 ||
  rwrtTac162 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t811.

(***********************
  End of filter
 ***********************)


(***********************
  Start of withFilter
 ***********************)

Definition withFilter1 (T: Type) (thiss72: List T) (p14: T -> bool) : List T :=
proj1_sig (filter1 T thiss72 p14).

Fail Next Obligation.

Hint Unfold withFilter1: definitions.

(***********************
  End of withFilter
 ***********************)
