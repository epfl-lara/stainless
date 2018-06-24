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

Ltac t767 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t768 :=
  t767 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t768.


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

Lemma None_exists: (forall T: Type, forall self576: Option T, ((true = isNone T self576)) <-> (((None_construct T = self576)))). 
Proof.
	repeat t768 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self577: Option T, ((true = isSome T self577)) <-> ((exists tmp216: T, (Some_construct T tmp216 = self577)))). 
Proof.
	repeat t768 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic72 := match goal with 
	| [ H288: (true = isNone ?T ?self578) |- _ ] => 
			poseNew (Mark (T,self578) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H288)
	| [ H288: (isNone ?T ?self578 = true) |- _ ] => 
			poseNew (Mark (T,self578) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H288))
	| [ H289: (true = isSome ?T ?self579) |- _ ] => 
			poseNew (Mark (T,self579) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H289)
	| [ H289: (isSome ?T ?self579 = true) |- _ ] => 
			poseNew (Mark (T,self579) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H289))
	| _ => idtac
end.

Ltac t769 :=
  t_base ||
  Option_tactic72 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t770 :=
  t769 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t770.


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

Lemma Cons_exists: (forall T: Type, forall self580: List T, ((true = isCons T self580)) <-> ((exists tmp218: List T, exists tmp217: T, (Cons_construct T tmp217 tmp218 = self580)))). 
Proof.
	repeat t770 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self581: List T, ((true = isNil T self581)) <-> (((Nil_construct T = self581)))). 
Proof.
	repeat t770 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic72 := match goal with 
	| [ H290: (true = isCons ?T ?self582) |- _ ] => 
			poseNew (Mark (T,self582) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H290)
	| [ H290: (isCons ?T ?self582 = true) |- _ ] => 
			poseNew (Mark (T,self582) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H290))
	| [ H291: (true = isNil ?T ?self583) |- _ ] => 
			poseNew (Mark (T,self583) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H291)
	| [ H291: (isNil ?T ?self583 = true) |- _ ] => 
			poseNew (Mark (T,self583) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H291))
	| _ => Option_tactic72
end.

Ltac t771 :=
  t_base ||
  List_tactic72 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t772 :=
  t771 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t772.

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
Definition content_rt37_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt37_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt37_type T thiss1 := 
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

Ltac rwrtTac_A153 := match goal with 
	| [ H1445: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B153 := match goal with 
	| [ H1445: context[content ?T ?thiss1], H2445: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2445: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac153 := idtac; repeat rwrtTac_A153; repeat rwrtTac_B153.

Ltac t773 :=
  t_base ||
  List_tactic72 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t774 :=
  t773 ||
  rwrtTac153 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t774.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt34_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt34_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt34_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A154 := match goal with 
	| [ H1446: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B154 := match goal with 
	| [ H1446: context[size ?T ?thiss30], H2446: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2446: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac154 := rwrtTac153; repeat rwrtTac_A154; repeat rwrtTac_B154.

Ltac t775 :=
  t_base ||
  List_tactic72 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t776 :=
  t775 ||
  rwrtTac154 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t776.

(***********************
  End of size
 ***********************)

(***********************
  Start of -
 ***********************)

Obligation Tactic:=idtac.
Definition minus__rt1_type (T: Type) (thiss33: List T) (e: T) : Type :=
{res4: List T | (ifthenelse (Z.leb (proj1_sig (size T res4)) (proj1_sig (size T thiss33))) bool
	(fun _ => set_equality (content T res4) (set_difference (content T thiss33) (set_union (@set_empty T) (set_singleton e))) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold minus__rt1_type.


Equations (noind) minus_ (T: Type) (thiss33: List T) (e: T) : minus__rt1_type T thiss33 e := 
	minus_ T thiss33 e by rec ignore_termination lt :=
	minus_ T thiss33 e := match thiss33 with
	| Cons_construct _ h14 t286 => 
			ifthenelse (propInBool ((e = h14))) (List T)
				(fun _ => proj1_sig (minus_ T t286 e) )
				(fun _ => Cons_construct T h14 (proj1_sig (minus_ T t286 e)) )
	| Nil_construct _ => Nil_construct T
	end.

Hint Unfold minus__comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A155 := match goal with 
	| [ H1447: context[minus_ ?T ?thiss33 ?e] |- _ ] => 
			poseNew (Mark (T,thiss33,e) "unfolding minus__equation")
	| [  |- context[minus_ ?T ?thiss33 ?e] ] => 
			poseNew (Mark (T,thiss33,e) "unfolding minus__equation")
end.

Ltac rwrtTac_B155 := match goal with 
	| [ H1447: context[minus_ ?T ?thiss33 ?e], H2447: Marked (?T,?thiss33,?e) "unfolding minus__equation" |- _ ] => 
			poseNew (Mark (T,thiss33,e) "unfolded minus__equation");
			add_equation (minus__equation_1 T thiss33 e)
	| [ H2447: Marked (?T,?thiss33,?e) "unfolding minus__equation" |- context[minus_ ?T ?thiss33 ?e] ] => 
			poseNew (Mark (T,thiss33,e) "unfolded minus__equation");
			add_equation (minus__equation_1 T thiss33 e)
end.

Ltac rwrtTac155 := rwrtTac154; repeat rwrtTac_A155; repeat rwrtTac_B155.

Ltac t777 :=
  t_base ||
  List_tactic72 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t778 :=
  t777 ||
  rwrtTac155 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t778.

(***********************
  End of -
 ***********************)


(***********************
  Start of unique
 ***********************)


Definition unique_rt_type (T: Type) (thiss69: List T) : Type :=
List T.

Fail Next Obligation.

Hint Unfold unique_rt_type.


Equations (noind) unique (T: Type) (thiss69: List T) : unique_rt_type T thiss69 := 
	unique T thiss69 by rec ignore_termination lt :=
	unique T thiss69 := match thiss69 with
	| Nil_construct _ => Nil_construct T
	| Cons_construct _ h27 t779 => 
			Cons_construct T h27 (proj1_sig (minus_ T (unique T t779) h27))
	end.

Hint Unfold unique_comp_proj.

Solve Obligations with (repeat t778).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A156 := match goal with 
	| [ H1448: context[unique ?T ?thiss69] |- _ ] => 
			poseNew (Mark (T,thiss69) "unfolding unique_equation")
	| [  |- context[unique ?T ?thiss69] ] => 
			poseNew (Mark (T,thiss69) "unfolding unique_equation")
end.

Ltac rwrtTac_B156 := match goal with 
	| [ H1448: context[unique ?T ?thiss69], H2448: Marked (?T,?thiss69) "unfolding unique_equation" |- _ ] => 
			poseNew (Mark (T,thiss69) "unfolded unique_equation");
			add_equation (unique_equation_1 T thiss69)
	| [ H2448: Marked (?T,?thiss69) "unfolding unique_equation" |- context[unique ?T ?thiss69] ] => 
			poseNew (Mark (T,thiss69) "unfolded unique_equation");
			add_equation (unique_equation_1 T thiss69)
end.

Ltac rwrtTac156 := rwrtTac155; repeat rwrtTac_A156; repeat rwrtTac_B156.

Ltac t780 :=
  t_base ||
  List_tactic72 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t781 :=
  t780 ||
  rwrtTac156 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t781.

(***********************
  End of unique
 ***********************)
