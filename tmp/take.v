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

Ltac t665 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t666 :=
  t665 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t666.


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

Lemma None_exists: (forall T: Type, forall self512: Option T, ((true = isNone T self512)) <-> (((None_construct T = self512)))). 
Proof.
	repeat t666 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self513: Option T, ((true = isSome T self513)) <-> ((exists tmp192: T, (Some_construct T tmp192 = self513)))). 
Proof.
	repeat t666 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic64 := match goal with 
	| [ H256: (true = isNone ?T ?self514) |- _ ] => 
			poseNew (Mark (T,self514) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H256)
	| [ H256: (isNone ?T ?self514 = true) |- _ ] => 
			poseNew (Mark (T,self514) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H256))
	| [ H257: (true = isSome ?T ?self515) |- _ ] => 
			poseNew (Mark (T,self515) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H257)
	| [ H257: (isSome ?T ?self515 = true) |- _ ] => 
			poseNew (Mark (T,self515) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H257))
	| _ => idtac
end.

Ltac t667 :=
  t_base ||
  Option_tactic64 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t668 :=
  t667 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t668.


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

Lemma Cons_exists: (forall T: Type, forall self516: List T, ((true = isCons T self516)) <-> ((exists tmp194: List T, exists tmp193: T, (Cons_construct T tmp193 tmp194 = self516)))). 
Proof.
	repeat t668 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self517: List T, ((true = isNil T self517)) <-> (((Nil_construct T = self517)))). 
Proof.
	repeat t668 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic64 := match goal with 
	| [ H258: (true = isCons ?T ?self518) |- _ ] => 
			poseNew (Mark (T,self518) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H258)
	| [ H258: (isCons ?T ?self518 = true) |- _ ] => 
			poseNew (Mark (T,self518) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H258))
	| [ H259: (true = isNil ?T ?self519) |- _ ] => 
			poseNew (Mark (T,self519) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H259)
	| [ H259: (isNil ?T ?self519 = true) |- _ ] => 
			poseNew (Mark (T,self519) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H259))
	| _ => Option_tactic64
end.

Ltac t669 :=
  t_base ||
  List_tactic64 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t670 :=
  t669 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t670.

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
Definition content_rt31_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt31_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt31_type T thiss1 := 
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

Ltac rwrtTac_A126 := match goal with 
	| [ H1386: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B126 := match goal with 
	| [ H1386: context[content ?T ?thiss1], H2386: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2386: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac126 := idtac; repeat rwrtTac_A126; repeat rwrtTac_B126.

Ltac t671 :=
  t_base ||
  List_tactic64 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t672 :=
  t671 ||
  rwrtTac126 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t672.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt28_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt28_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt28_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A127 := match goal with 
	| [ H1387: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B127 := match goal with 
	| [ H1387: context[size ?T ?thiss30], H2387: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2387: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac127 := rwrtTac126; repeat rwrtTac_A127; repeat rwrtTac_B127.

Ltac t673 :=
  t_base ||
  List_tactic64 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t674 :=
  t673 ||
  rwrtTac127 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t674.

(***********************
  End of size
 ***********************)


(***********************
  Start of take
 ***********************)


Definition take_rt_type (T: Type) (thiss61: List T) (i1: Z) : Type :=
{res22: List T | (ifthenelse (set_subset (content T res22) (content T thiss61)) bool
	(fun _ => Zeq_bool (proj1_sig (size T res22)) (ifthenelse (Z.leb i1 (0)%Z) Z
		(fun _ => (0)%Z )
		(fun _ => ifthenelse (Z.geb i1 (proj1_sig (size T thiss61))) Z
			(fun _ => proj1_sig (size T thiss61) )
			(fun _ => i1 ) )) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold take_rt_type.


Equations (noind) take (T: Type) (thiss61: List T) (i1: Z) : take_rt_type T thiss61 i1 := 
	take T thiss61 i1 by rec ignore_termination lt :=
	take T thiss61 i1 := ifthenelse (isNil _ thiss61) (List T)
		(fun _ => Nil_construct T )
		(fun _ => ifthenelse (isCons _ thiss61) (List T)
			(fun _ => ifthenelse (Z.leb i1 (0)%Z) (List T)
				(fun _ => Nil_construct T )
				(fun _ => Cons_construct T (h T thiss61) (proj1_sig (take T (t7 T thiss61) (Z.sub i1 (1)%Z))) ) )
			(fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold take_comp_proj.

Solve Obligations with (repeat t674).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A128 := match goal with 
	| [ H1388: context[take ?T ?thiss61 ?i1] |- _ ] => 
			poseNew (Mark (T,thiss61,i1) "unfolding take_equation")
	| [  |- context[take ?T ?thiss61 ?i1] ] => 
			poseNew (Mark (T,thiss61,i1) "unfolding take_equation")
end.

Ltac rwrtTac_B128 := match goal with 
	| [ H1388: context[take ?T ?thiss61 ?i1], H2388: Marked (?T,?thiss61,?i1) "unfolding take_equation" |- _ ] => 
			poseNew (Mark (T,thiss61,i1) "unfolded take_equation");
			add_equation (take_equation_1 T thiss61 i1)
	| [ H2388: Marked (?T,?thiss61,?i1) "unfolding take_equation" |- context[take ?T ?thiss61 ?i1] ] => 
			poseNew (Mark (T,thiss61,i1) "unfolded take_equation");
			add_equation (take_equation_1 T thiss61 i1)
end.

Ltac rwrtTac128 := rwrtTac127; repeat rwrtTac_A128; repeat rwrtTac_B128.

Ltac t675 :=
  t_base ||
  List_tactic64 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t676 :=
  t675 ||
  rwrtTac128 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t676.

(***********************
  End of take
 ***********************)
