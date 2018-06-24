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

Ltac t401 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t402 :=
  t401 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t402.


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

Lemma None_exists: (forall T: Type, forall self344: Option T, ((true = isNone T self344)) <-> (((None_construct T = self344)))). 
Proof.
	repeat t402 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self345: Option T, ((true = isSome T self345)) <-> ((exists tmp129: T, (Some_construct T tmp129 = self345)))). 
Proof.
	repeat t402 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic43 := match goal with 
	| [ H172: (true = isNone ?T ?self346) |- _ ] => 
			poseNew (Mark (T,self346) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H172)
	| [ H172: (isNone ?T ?self346 = true) |- _ ] => 
			poseNew (Mark (T,self346) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H172))
	| [ H173: (true = isSome ?T ?self347) |- _ ] => 
			poseNew (Mark (T,self347) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H173)
	| [ H173: (isSome ?T ?self347 = true) |- _ ] => 
			poseNew (Mark (T,self347) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H173))
	| _ => idtac
end.

Ltac t403 :=
  t_base ||
  Option_tactic43 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t404 :=
  t403 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t404.


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

Lemma Cons_exists: (forall T: Type, forall self348: List T, ((true = isCons T self348)) <-> ((exists tmp131: List T, exists tmp130: T, (Cons_construct T tmp130 tmp131 = self348)))). 
Proof.
	repeat t404 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self349: List T, ((true = isNil T self349)) <-> (((Nil_construct T = self349)))). 
Proof.
	repeat t404 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic43 := match goal with 
	| [ H174: (true = isCons ?T ?self350) |- _ ] => 
			poseNew (Mark (T,self350) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H174)
	| [ H174: (isCons ?T ?self350 = true) |- _ ] => 
			poseNew (Mark (T,self350) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H174))
	| [ H175: (true = isNil ?T ?self351) |- _ ] => 
			poseNew (Mark (T,self351) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H175)
	| [ H175: (isNil ?T ?self351 = true) |- _ ] => 
			poseNew (Mark (T,self351) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H175))
	| _ => Option_tactic43
end.

Ltac t405 :=
  t_base ||
  List_tactic43 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t406 :=
  t405 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t406.

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
Definition content_rt16_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt16_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt16_type T thiss1 := 
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

Ltac rwrtTac_A61 := match goal with 
	| [ H1237: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B61 := match goal with 
	| [ H1237: context[content ?T ?thiss1], H2237: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2237: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac61 := idtac; repeat rwrtTac_A61; repeat rwrtTac_B61.

Ltac t407 :=
  t_base ||
  List_tactic43 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t408 :=
  t407 ||
  rwrtTac61 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t408.

(***********************
  End of content
 ***********************)

(***********************
  Start of forall
 ***********************)

Obligation Tactic:=idtac.
Definition _forall_rt5_type (T: Type) (thiss8: List T) (p2: T -> bool) : Type :=
bool.

Fail Next Obligation.

Hint Unfold _forall_rt5_type.


Equations (noind) _forall (T: Type) (thiss8: List T) (p2: T -> bool) : _forall_rt5_type T thiss8 p2 := 
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

Ltac rwrtTac_A62 := match goal with 
	| [ H1238: context[_forall ?T ?thiss8 ?p2] |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
	| [  |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
end.

Ltac rwrtTac_B62 := match goal with 
	| [ H1238: context[_forall ?T ?thiss8 ?p2], H2238: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
	| [ H2238: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
end.

Ltac rwrtTac62 := rwrtTac61; repeat rwrtTac_A62; repeat rwrtTac_B62.

Ltac t409 :=
  t_base ||
  List_tactic43 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t410 :=
  t409 ||
  rwrtTac62 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t410.

(***********************
  End of forall
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt12_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt12_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt12_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A63 := match goal with 
	| [ H1239: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B63 := match goal with 
	| [ H1239: context[size ?T ?thiss30], H2239: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2239: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac63 := rwrtTac62; repeat rwrtTac_A63; repeat rwrtTac_B63.

Ltac t411 :=
  t_base ||
  List_tactic43 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t412 :=
  t411 ||
  rwrtTac63 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t412.

(***********************
  End of size
 ***********************)

(***********************
  Start of filter
 ***********************)

Obligation Tactic:=idtac.
Definition filter1_rt2_type (T: Type) (thiss40: List T) (p8: T -> bool) : Type :=
{res10: List T | (ifthenelse
	(ifthenelse (Z.leb (proj1_sig (size T res10)) (proj1_sig (size T thiss40))) bool
		(fun _ => set_subset (content T res10) (content T thiss40) )
		(fun _ => false ))
	bool
	(fun _ => _forall T res10 p8 )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold filter1_rt2_type.


Equations (noind) filter1 (T: Type) (thiss40: List T) (p8: T -> bool) : filter1_rt2_type T thiss40 p8 := 
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

Ltac rwrtTac_A64 := match goal with 
	| [ H1240: context[filter1 ?T ?thiss40 ?p8] |- _ ] => 
			poseNew (Mark (T,thiss40,p8) "unfolding filter1_equation")
	| [  |- context[filter1 ?T ?thiss40 ?p8] ] => 
			poseNew (Mark (T,thiss40,p8) "unfolding filter1_equation")
end.

Ltac rwrtTac_B64 := match goal with 
	| [ H1240: context[filter1 ?T ?thiss40 ?p8], H2240: Marked (?T,?thiss40,?p8) "unfolding filter1_equation" |- _ ] => 
			poseNew (Mark (T,thiss40,p8) "unfolded filter1_equation");
			add_equation (filter1_equation_1 T thiss40 p8)
	| [ H2240: Marked (?T,?thiss40,?p8) "unfolding filter1_equation" |- context[filter1 ?T ?thiss40 ?p8] ] => 
			poseNew (Mark (T,thiss40,p8) "unfolded filter1_equation");
			add_equation (filter1_equation_1 T thiss40 p8)
end.

Ltac rwrtTac64 := rwrtTac63; repeat rwrtTac_A64; repeat rwrtTac_B64.

Ltac t413 :=
  t_base ||
  List_tactic43 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t414 :=
  t413 ||
  rwrtTac64 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t414.

(***********************
  End of filter
 ***********************)


(***********************
  Start of filterNot
 ***********************)

Definition filterNot (T: Type) (thiss42: List T) (p10: T -> bool) : {res11: List T | (ifthenelse
	(ifthenelse (Z.leb (proj1_sig (size T res11)) (proj1_sig (size T thiss42))) bool
		(fun _ => set_subset (content T res11) (content T thiss42) )
		(fun _ => false ))
	bool
	(fun _ => _forall T res11 (fun x___18 => negb (p10 x___18) ) )
	(fun _ => false ) = true)} :=
proj1_sig (filter1 T thiss42 (fun x___17 => negb (p10 x___17) )).

Fail Next Obligation.

Hint Unfold filterNot: definitions.

(***********************
  End of filterNot
 ***********************)
