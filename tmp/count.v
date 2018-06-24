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

Ltac t384 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t385 :=
  t384 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t385.


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

Lemma None_exists: (forall T: Type, forall self336: Option T, ((true = isNone T self336)) <-> (((None_construct T = self336)))). 
Proof.
	repeat t385 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self337: Option T, ((true = isSome T self337)) <-> ((exists tmp126: T, (Some_construct T tmp126 = self337)))). 
Proof.
	repeat t385 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic42 := match goal with 
	| [ H168: (true = isNone ?T ?self338) |- _ ] => 
			poseNew (Mark (T,self338) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H168)
	| [ H168: (isNone ?T ?self338 = true) |- _ ] => 
			poseNew (Mark (T,self338) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H168))
	| [ H169: (true = isSome ?T ?self339) |- _ ] => 
			poseNew (Mark (T,self339) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H169)
	| [ H169: (isSome ?T ?self339 = true) |- _ ] => 
			poseNew (Mark (T,self339) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H169))
	| _ => idtac
end.

Ltac t386 :=
  t_base ||
  Option_tactic42 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t387 :=
  t386 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t387.


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

Lemma Cons_exists: (forall T: Type, forall self340: List T, ((true = isCons T self340)) <-> ((exists tmp128: List T, exists tmp127: T, (Cons_construct T tmp127 tmp128 = self340)))). 
Proof.
	repeat t387 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self341: List T, ((true = isNil T self341)) <-> (((Nil_construct T = self341)))). 
Proof.
	repeat t387 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic42 := match goal with 
	| [ H170: (true = isCons ?T ?self342) |- _ ] => 
			poseNew (Mark (T,self342) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H170)
	| [ H170: (isCons ?T ?self342 = true) |- _ ] => 
			poseNew (Mark (T,self342) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H170))
	| [ H171: (true = isNil ?T ?self343) |- _ ] => 
			poseNew (Mark (T,self343) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H171)
	| [ H171: (isNil ?T ?self343 = true) |- _ ] => 
			poseNew (Mark (T,self343) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H171))
	| _ => Option_tactic42
end.

Ltac t388 :=
  t_base ||
  List_tactic42 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t389 :=
  t388 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t389.

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
Definition content_rt15_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt15_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt15_type T thiss1 := 
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

Ltac rwrtTac_A56 := match goal with 
	| [ H1228: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B56 := match goal with 
	| [ H1228: context[content ?T ?thiss1], H2228: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2228: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac56 := idtac; repeat rwrtTac_A56; repeat rwrtTac_B56.

Ltac t390 :=
  t_base ||
  List_tactic42 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t391 :=
  t390 ||
  rwrtTac56 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t391.

(***********************
  End of content
 ***********************)

(***********************
  Start of forall
 ***********************)

Obligation Tactic:=idtac.
Definition _forall_rt4_type (T: Type) (thiss8: List T) (p2: T -> bool) : Type :=
bool.

Fail Next Obligation.

Hint Unfold _forall_rt4_type.


Equations (noind) _forall (T: Type) (thiss8: List T) (p2: T -> bool) : _forall_rt4_type T thiss8 p2 := 
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

Ltac rwrtTac_A57 := match goal with 
	| [ H1229: context[_forall ?T ?thiss8 ?p2] |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
	| [  |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
end.

Ltac rwrtTac_B57 := match goal with 
	| [ H1229: context[_forall ?T ?thiss8 ?p2], H2229: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
	| [ H2229: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
end.

Ltac rwrtTac57 := rwrtTac56; repeat rwrtTac_A57; repeat rwrtTac_B57.

Ltac t392 :=
  t_base ||
  List_tactic42 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t393 :=
  t392 ||
  rwrtTac57 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t393.

(***********************
  End of forall
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt11_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt11_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt11_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A58 := match goal with 
	| [ H1230: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B58 := match goal with 
	| [ H1230: context[size ?T ?thiss30], H2230: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2230: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac58 := rwrtTac57; repeat rwrtTac_A58; repeat rwrtTac_B58.

Ltac t394 :=
  t_base ||
  List_tactic42 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t395 :=
  t394 ||
  rwrtTac58 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t395.

(***********************
  End of size
 ***********************)

(***********************
  Start of filter
 ***********************)

Obligation Tactic:=idtac.
Definition filter1_rt1_type (T: Type) (thiss40: List T) (p8: T -> bool) : Type :=
{res10: List T | (ifthenelse
	(ifthenelse (Z.leb (proj1_sig (size T res10)) (proj1_sig (size T thiss40))) bool
		(fun _ => set_subset (content T res10) (content T thiss40) )
		(fun _ => false ))
	bool
	(fun _ => _forall T res10 p8 )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold filter1_rt1_type.


Equations (noind) filter1 (T: Type) (thiss40: List T) (p8: T -> bool) : filter1_rt1_type T thiss40 p8 := 
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

Ltac rwrtTac_A59 := match goal with 
	| [ H1231: context[filter1 ?T ?thiss40 ?p8] |- _ ] => 
			poseNew (Mark (T,thiss40,p8) "unfolding filter1_equation")
	| [  |- context[filter1 ?T ?thiss40 ?p8] ] => 
			poseNew (Mark (T,thiss40,p8) "unfolding filter1_equation")
end.

Ltac rwrtTac_B59 := match goal with 
	| [ H1231: context[filter1 ?T ?thiss40 ?p8], H2231: Marked (?T,?thiss40,?p8) "unfolding filter1_equation" |- _ ] => 
			poseNew (Mark (T,thiss40,p8) "unfolded filter1_equation");
			add_equation (filter1_equation_1 T thiss40 p8)
	| [ H2231: Marked (?T,?thiss40,?p8) "unfolding filter1_equation" |- context[filter1 ?T ?thiss40 ?p8] ] => 
			poseNew (Mark (T,thiss40,p8) "unfolded filter1_equation");
			add_equation (filter1_equation_1 T thiss40 p8)
end.

Ltac rwrtTac59 := rwrtTac58; repeat rwrtTac_A59; repeat rwrtTac_B59.

Ltac t396 :=
  t_base ||
  List_tactic42 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t397 :=
  t396 ||
  rwrtTac59 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t397.

(***********************
  End of filter
 ***********************)


(***********************
  Start of count
 ***********************)


Definition count_rt_type (T: Type) (thiss41: List T) (p9: T -> bool) : Type :=
{x___24: Z | (Zeq_bool x___24 (proj1_sig (size T (proj1_sig (filter1 T thiss41 p9)))) = true)}.

Fail Next Obligation.

Hint Unfold count_rt_type.


Equations (noind) count (T: Type) (thiss41: List T) (p9: T -> bool) : count_rt_type T thiss41 p9 := 
	count T thiss41 p9 by rec ignore_termination lt :=
	count T thiss41 p9 := match thiss41 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h17 t398 => 
			Z.add (ifthenelse (p9 h17) Z
				(fun _ => (1)%Z )
				(fun _ => (0)%Z )) (proj1_sig (count T t398 p9))
	end.

Hint Unfold count_comp_proj.

Solve Obligations with (repeat t397).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A60 := match goal with 
	| [ H1232: context[count ?T ?thiss41 ?p9] |- _ ] => 
			poseNew (Mark (T,thiss41,p9) "unfolding count_equation")
	| [  |- context[count ?T ?thiss41 ?p9] ] => 
			poseNew (Mark (T,thiss41,p9) "unfolding count_equation")
end.

Ltac rwrtTac_B60 := match goal with 
	| [ H1232: context[count ?T ?thiss41 ?p9], H2232: Marked (?T,?thiss41,?p9) "unfolding count_equation" |- _ ] => 
			poseNew (Mark (T,thiss41,p9) "unfolded count_equation");
			add_equation (count_equation_1 T thiss41 p9)
	| [ H2232: Marked (?T,?thiss41,?p9) "unfolding count_equation" |- context[count ?T ?thiss41 ?p9] ] => 
			poseNew (Mark (T,thiss41,p9) "unfolded count_equation");
			add_equation (count_equation_1 T thiss41 p9)
end.

Ltac rwrtTac60 := rwrtTac59; repeat rwrtTac_A60; repeat rwrtTac_B60.

Ltac t399 :=
  t_base ||
  List_tactic42 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t400 :=
  t399 ||
  rwrtTac60 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t400.

(***********************
  End of count
 ***********************)
