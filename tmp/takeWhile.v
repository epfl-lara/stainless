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

Ltac t739 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t740 :=
  t739 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t740.


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

Lemma None_exists: (forall T: Type, forall self552: Option T, ((true = isNone T self552)) <-> (((None_construct T = self552)))). 
Proof.
	repeat t740 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self553: Option T, ((true = isSome T self553)) <-> ((exists tmp207: T, (Some_construct T tmp207 = self553)))). 
Proof.
	repeat t740 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic69 := match goal with 
	| [ H276: (true = isNone ?T ?self554) |- _ ] => 
			poseNew (Mark (T,self554) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H276)
	| [ H276: (isNone ?T ?self554 = true) |- _ ] => 
			poseNew (Mark (T,self554) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H276))
	| [ H277: (true = isSome ?T ?self555) |- _ ] => 
			poseNew (Mark (T,self555) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H277)
	| [ H277: (isSome ?T ?self555 = true) |- _ ] => 
			poseNew (Mark (T,self555) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H277))
	| _ => idtac
end.

Ltac t741 :=
  t_base ||
  Option_tactic69 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t742 :=
  t741 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t742.


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

Lemma Cons_exists: (forall T: Type, forall self556: List T, ((true = isCons T self556)) <-> ((exists tmp209: List T, exists tmp208: T, (Cons_construct T tmp208 tmp209 = self556)))). 
Proof.
	repeat t742 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self557: List T, ((true = isNil T self557)) <-> (((Nil_construct T = self557)))). 
Proof.
	repeat t742 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic69 := match goal with 
	| [ H278: (true = isCons ?T ?self558) |- _ ] => 
			poseNew (Mark (T,self558) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H278)
	| [ H278: (isCons ?T ?self558 = true) |- _ ] => 
			poseNew (Mark (T,self558) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H278))
	| [ H279: (true = isNil ?T ?self559) |- _ ] => 
			poseNew (Mark (T,self559) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H279)
	| [ H279: (isNil ?T ?self559 = true) |- _ ] => 
			poseNew (Mark (T,self559) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H279))
	| _ => Option_tactic69
end.

Ltac t743 :=
  t_base ||
  List_tactic69 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t744 :=
  t743 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t744.

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
Definition content_rt36_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt36_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt36_type T thiss1 := 
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

Ltac rwrtTac_A148 := match goal with 
	| [ H1428: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B148 := match goal with 
	| [ H1428: context[content ?T ?thiss1], H2428: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2428: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac148 := idtac; repeat rwrtTac_A148; repeat rwrtTac_B148.

Ltac t745 :=
  t_base ||
  List_tactic69 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t746 :=
  t745 ||
  rwrtTac148 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t746.

(***********************
  End of content
 ***********************)

(***********************
  Start of forall
 ***********************)

Obligation Tactic:=idtac.
Definition _forall_rt7_type (T: Type) (thiss8: List T) (p2: T -> bool) : Type :=
bool.

Fail Next Obligation.

Hint Unfold _forall_rt7_type.


Equations (noind) _forall (T: Type) (thiss8: List T) (p2: T -> bool) : _forall_rt7_type T thiss8 p2 := 
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

Ltac rwrtTac_A149 := match goal with 
	| [ H1429: context[_forall ?T ?thiss8 ?p2] |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
	| [  |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
end.

Ltac rwrtTac_B149 := match goal with 
	| [ H1429: context[_forall ?T ?thiss8 ?p2], H2429: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
	| [ H2429: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
end.

Ltac rwrtTac149 := rwrtTac148; repeat rwrtTac_A149; repeat rwrtTac_B149.

Ltac t747 :=
  t_base ||
  List_tactic69 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t748 :=
  t747 ||
  rwrtTac149 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t748.

(***********************
  End of forall
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt33_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt33_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt33_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A150 := match goal with 
	| [ H1430: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B150 := match goal with 
	| [ H1430: context[size ?T ?thiss30], H2430: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2430: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac150 := rwrtTac149; repeat rwrtTac_A150; repeat rwrtTac_B150.

Ltac t749 :=
  t_base ||
  List_tactic69 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t750 :=
  t749 ||
  rwrtTac150 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t750.

(***********************
  End of size
 ***********************)


(***********************
  Start of takeWhile
 ***********************)


Definition takeWhile_rt_type (T: Type) (thiss66: List T) (p12: T -> bool) : Type :=
{res25: List T | (ifthenelse
	(ifthenelse (_forall T res25 p12) bool
		(fun _ => Z.leb (proj1_sig (size T res25)) (proj1_sig (size T thiss66)) )
		(fun _ => false ))
	bool
	(fun _ => set_subset (content T res25) (content T thiss66) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold takeWhile_rt_type.


Equations (noind) takeWhile (T: Type) (thiss66: List T) (p12: T -> bool) : takeWhile_rt_type T thiss66 p12 := 
	takeWhile T thiss66 p12 by rec ignore_termination lt :=
	takeWhile T thiss66 p12 := ifthenelse
		(ifthenelse (isCons _ thiss66) bool
			(fun _ => p12 (h T thiss66) )
			(fun _ => false ))
		(List T)
		(fun _ => Cons_construct T (h T thiss66) (proj1_sig (takeWhile T (t7 T thiss66) p12)) )
		(fun _ => Nil_construct T ).

Hint Unfold takeWhile_comp_proj.

Solve Obligations with (repeat t750).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A151 := match goal with 
	| [ H1431: context[takeWhile ?T ?thiss66 ?p12] |- _ ] => 
			poseNew (Mark (T,thiss66,p12) "unfolding takeWhile_equation")
	| [  |- context[takeWhile ?T ?thiss66 ?p12] ] => 
			poseNew (Mark (T,thiss66,p12) "unfolding takeWhile_equation")
end.

Ltac rwrtTac_B151 := match goal with 
	| [ H1431: context[takeWhile ?T ?thiss66 ?p12], H2431: Marked (?T,?thiss66,?p12) "unfolding takeWhile_equation" |- _ ] => 
			poseNew (Mark (T,thiss66,p12) "unfolded takeWhile_equation");
			add_equation (takeWhile_equation_1 T thiss66 p12)
	| [ H2431: Marked (?T,?thiss66,?p12) "unfolding takeWhile_equation" |- context[takeWhile ?T ?thiss66 ?p12] ] => 
			poseNew (Mark (T,thiss66,p12) "unfolded takeWhile_equation");
			add_equation (takeWhile_equation_1 T thiss66 p12)
end.

Ltac rwrtTac151 := rwrtTac150; repeat rwrtTac_A151; repeat rwrtTac_B151.

Ltac t751 :=
  t_base ||
  List_tactic69 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t752 :=
  t751 ||
  rwrtTac151 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t752.

(***********************
  End of takeWhile
 ***********************)
