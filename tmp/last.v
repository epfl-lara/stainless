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

Ltac t177 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t178 :=
  t177 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t178.


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

Lemma None_exists: (forall T: Type, forall self184: Option T, ((true = isNone T self184)) <-> (((None_construct T = self184)))). 
Proof.
	repeat t178 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self185: Option T, ((true = isSome T self185)) <-> ((exists tmp69: T, (Some_construct T tmp69 = self185)))). 
Proof.
	repeat t178 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic23 := match goal with 
	| [ H92: (true = isNone ?T ?self186) |- _ ] => 
			poseNew (Mark (T,self186) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H92)
	| [ H92: (isNone ?T ?self186 = true) |- _ ] => 
			poseNew (Mark (T,self186) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H92))
	| [ H93: (true = isSome ?T ?self187) |- _ ] => 
			poseNew (Mark (T,self187) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H93)
	| [ H93: (isSome ?T ?self187 = true) |- _ ] => 
			poseNew (Mark (T,self187) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H93))
	| _ => idtac
end.

Ltac t179 :=
  t_base ||
  Option_tactic23 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t180 :=
  t179 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t180.


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

Lemma Cons_exists: (forall T: Type, forall self188: List T, ((true = isCons T self188)) <-> ((exists tmp71: List T, exists tmp70: T, (Cons_construct T tmp70 tmp71 = self188)))). 
Proof.
	repeat t180 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self189: List T, ((true = isNil T self189)) <-> (((Nil_construct T = self189)))). 
Proof.
	repeat t180 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic23 := match goal with 
	| [ H94: (true = isCons ?T ?self190) |- _ ] => 
			poseNew (Mark (T,self190) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H94)
	| [ H94: (isCons ?T ?self190 = true) |- _ ] => 
			poseNew (Mark (T,self190) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H94))
	| [ H95: (true = isNil ?T ?self191) |- _ ] => 
			poseNew (Mark (T,self191) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H95)
	| [ H95: (isNil ?T ?self191 = true) |- _ ] => 
			poseNew (Mark (T,self191) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H95))
	| _ => Option_tactic23
end.

Ltac t181 :=
  t_base ||
  List_tactic23 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t182 :=
  t181 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t182.

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
Definition content_rt4_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt4_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt4_type T thiss1 := 
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

Ltac rwrtTac_A14 := match goal with 
	| [ H1110: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B14 := match goal with 
	| [ H1110: context[content ?T ?thiss1], H2110: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2110: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac14 := idtac; repeat rwrtTac_A14; repeat rwrtTac_B14.

Ltac t183 :=
  t_base ||
  List_tactic23 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t184 :=
  t183 ||
  rwrtTac14 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t184.

(***********************
  End of content
 ***********************)

(***********************
  Start of contains
 ***********************)

Obligation Tactic:=idtac.
Definition contains_rt1_type (T: Type) (thiss2: List T) (v1: T) : Type :=
{x___2: bool | (Bool.eqb x___2 (set_elem_of v1 (content T thiss2)) = true)}.

Fail Next Obligation.

Hint Unfold contains_rt1_type.


Equations (noind) contains (T: Type) (thiss2: List T) (v1: T) : contains_rt1_type T thiss2 v1 := 
	contains T thiss2 v1 by rec ignore_termination lt :=
	contains T thiss2 v1 := match thiss2 with
	| Cons_construct _ h2 t26 => 
			ifthenelse (propInBool ((h2 = v1))) bool
				(fun _ => true )
				(fun _ => proj1_sig (contains T t26 v1) )
	| Nil_construct _ => false
	end.

Hint Unfold contains_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A15 := match goal with 
	| [ H1111: context[contains ?T ?thiss2 ?v1] |- _ ] => 
			poseNew (Mark (T,thiss2,v1) "unfolding contains_equation")
	| [  |- context[contains ?T ?thiss2 ?v1] ] => 
			poseNew (Mark (T,thiss2,v1) "unfolding contains_equation")
end.

Ltac rwrtTac_B15 := match goal with 
	| [ H1111: context[contains ?T ?thiss2 ?v1], H2111: Marked (?T,?thiss2,?v1) "unfolding contains_equation" |- _ ] => 
			poseNew (Mark (T,thiss2,v1) "unfolded contains_equation");
			add_equation (contains_equation_1 T thiss2 v1)
	| [ H2111: Marked (?T,?thiss2,?v1) "unfolding contains_equation" |- context[contains ?T ?thiss2 ?v1] ] => 
			poseNew (Mark (T,thiss2,v1) "unfolded contains_equation");
			add_equation (contains_equation_1 T thiss2 v1)
end.

Ltac rwrtTac15 := rwrtTac14; repeat rwrtTac_A15; repeat rwrtTac_B15.

Ltac t185 :=
  t_base ||
  List_tactic23 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t186 :=
  t185 ||
  rwrtTac15 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t186.

(***********************
  End of contains
 ***********************)

(***********************
  Start of isEmpty
 ***********************)

Definition isEmpty (T: Type) (thiss17: List T) : bool :=
ifthenelse (isNil _ thiss17) bool
	(fun _ => true )
	(fun _ => false ).

Fail Next Obligation.

Hint Unfold isEmpty: definitions.

(***********************
  End of isEmpty
 ***********************)


(***********************
  Start of last
 ***********************)


Definition contractHyp41_type (T: Type) (thiss22: List T) : Type :=
(negb (isEmpty T thiss22) = true).

Fail Next Obligation.

Hint Unfold contractHyp41_type.


Definition last_rt_type (T: Type) (thiss22: List T) (contractHyp41: contractHyp41_type T thiss22) : Type :=
{v3: T | (proj1_sig (contains T thiss22 v3) = true)}.

Fail Next Obligation.

Hint Unfold last_rt_type.


Equations (noind) last (T: Type) (thiss22: List T) (contractHyp41: contractHyp41_type T thiss22) : last_rt_type T thiss22 contractHyp41 := 
	last T thiss22 contractHyp41 by rec ignore_termination lt :=
	last T thiss22 contractHyp41 := ifthenelse
		(ifthenelse (isCons _ thiss22) bool
			(fun _ => isNil _ (t7 T thiss22) )
			(fun _ => false ))
		T
		(fun _ => h T thiss22 )
		(fun _ => ifthenelse (isCons _ thiss22) T
			(fun _ => proj1_sig (last T (t7 T thiss22) _) )
			(fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold last_comp_proj.

Solve Obligations with (repeat t186).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A16 := match goal with 
	| [ H1112: context[last ?T ?thiss22] |- _ ] => 
			poseNew (Mark (T,thiss22) "unfolding last_equation")
	| [  |- context[last ?T ?thiss22] ] => 
			poseNew (Mark (T,thiss22) "unfolding last_equation")
end.

Ltac rwrtTac_B16 := match goal with 
	| [ H1112: context[last ?T ?thiss22], H2112: Marked (?T,?thiss22) "unfolding last_equation" |- _ ] => 
			poseNew (Mark (T,thiss22) "unfolded last_equation");
			add_equation (last_equation_1 T thiss22)
	| [ H2112: Marked (?T,?thiss22) "unfolding last_equation" |- context[last ?T ?thiss22] ] => 
			poseNew (Mark (T,thiss22) "unfolded last_equation");
			add_equation (last_equation_1 T thiss22)
end.

Ltac rwrtTac16 := rwrtTac15; repeat rwrtTac_A16; repeat rwrtTac_B16.

Ltac t187 :=
  t_base ||
  List_tactic23 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t188 :=
  t187 ||
  rwrtTac16 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t188.

(***********************
  End of last
 ***********************)
