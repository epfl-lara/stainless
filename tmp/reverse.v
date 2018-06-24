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

Ltac t595 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t596 :=
  t595 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t596.


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

Lemma None_exists: (forall T: Type, forall self456: Option T, ((true = isNone T self456)) <-> (((None_construct T = self456)))). 
Proof.
	repeat t596 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self457: Option T, ((true = isSome T self457)) <-> ((exists tmp171: T, (Some_construct T tmp171 = self457)))). 
Proof.
	repeat t596 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic57 := match goal with 
	| [ H228: (true = isNone ?T ?self458) |- _ ] => 
			poseNew (Mark (T,self458) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H228)
	| [ H228: (isNone ?T ?self458 = true) |- _ ] => 
			poseNew (Mark (T,self458) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H228))
	| [ H229: (true = isSome ?T ?self459) |- _ ] => 
			poseNew (Mark (T,self459) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H229)
	| [ H229: (isSome ?T ?self459 = true) |- _ ] => 
			poseNew (Mark (T,self459) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H229))
	| _ => idtac
end.

Ltac t597 :=
  t_base ||
  Option_tactic57 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t598 :=
  t597 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t598.


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

Lemma Cons_exists: (forall T: Type, forall self460: List T, ((true = isCons T self460)) <-> ((exists tmp173: List T, exists tmp172: T, (Cons_construct T tmp172 tmp173 = self460)))). 
Proof.
	repeat t598 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self461: List T, ((true = isNil T self461)) <-> (((Nil_construct T = self461)))). 
Proof.
	repeat t598 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic57 := match goal with 
	| [ H230: (true = isCons ?T ?self462) |- _ ] => 
			poseNew (Mark (T,self462) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H230)
	| [ H230: (isCons ?T ?self462 = true) |- _ ] => 
			poseNew (Mark (T,self462) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H230))
	| [ H231: (true = isNil ?T ?self463) |- _ ] => 
			poseNew (Mark (T,self463) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H231)
	| [ H231: (isNil ?T ?self463 = true) |- _ ] => 
			poseNew (Mark (T,self463) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H231))
	| _ => Option_tactic57
end.

Ltac t599 :=
  t_base ||
  List_tactic57 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t600 :=
  t599 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t600.

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
Definition content_rt28_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt28_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt28_type T thiss1 := 
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

Ltac rwrtTac_A113 := match goal with 
	| [ H1345: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B113 := match goal with 
	| [ H1345: context[content ?T ?thiss1], H2345: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2345: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac113 := idtac; repeat rwrtTac_A113; repeat rwrtTac_B113.

Ltac t601 :=
  t_base ||
  List_tactic57 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t602 :=
  t601 ||
  rwrtTac113 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t602.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt26_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt26_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt26_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A114 := match goal with 
	| [ H1346: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B114 := match goal with 
	| [ H1346: context[size ?T ?thiss30], H2346: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2346: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac114 := rwrtTac113; repeat rwrtTac_A114; repeat rwrtTac_B114.

Ltac t603 :=
  t_base ||
  List_tactic57 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t604 :=
  t603 ||
  rwrtTac114 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t604.

(***********************
  End of size
 ***********************)

(***********************
  Start of :+
 ***********************)

Obligation Tactic:=idtac.
Definition snoc__rt3_type (T: Type) (thiss35: List T) (t314: T) : Type :=
{res6: List T | (let assumption3 := (magic ((isCons _ res6 = true))) in (ifthenelse (Zeq_bool (proj1_sig (size T res6)) (Z.add (proj1_sig (size T thiss35)) (1)%Z)) bool
	(fun _ => set_equality (content T res6) (set_union (content T thiss35) (set_union (@set_empty T) (set_singleton t314))) )
	(fun _ => false )) = true)}.

Fail Next Obligation.

Hint Unfold snoc__rt3_type.


Equations (noind) snoc_ (T: Type) (thiss35: List T) (t314: T) : snoc__rt3_type T thiss35 t314 := 
	snoc_ T thiss35 t314 by rec ignore_termination lt :=
	snoc_ T thiss35 t314 := match thiss35 with
	| Nil_construct _ => Cons_construct T t314 thiss35
	| Cons_construct _ x3 xs1 => Cons_construct T x3 (proj1_sig (snoc_ T xs1 t314))
	end.

Hint Unfold snoc__comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A115 := match goal with 
	| [ H1347: context[snoc_ ?T ?thiss35 ?t314] |- _ ] => 
			poseNew (Mark (T,thiss35,t314) "unfolding snoc__equation")
	| [  |- context[snoc_ ?T ?thiss35 ?t314] ] => 
			poseNew (Mark (T,thiss35,t314) "unfolding snoc__equation")
end.

Ltac rwrtTac_B115 := match goal with 
	| [ H1347: context[snoc_ ?T ?thiss35 ?t314], H2347: Marked (?T,?thiss35,?t314) "unfolding snoc__equation" |- _ ] => 
			poseNew (Mark (T,thiss35,t314) "unfolded snoc__equation");
			add_equation (snoc__equation_1 T thiss35 t314)
	| [ H2347: Marked (?T,?thiss35,?t314) "unfolding snoc__equation" |- context[snoc_ ?T ?thiss35 ?t314] ] => 
			poseNew (Mark (T,thiss35,t314) "unfolded snoc__equation");
			add_equation (snoc__equation_1 T thiss35 t314)
end.

Ltac rwrtTac115 := rwrtTac114; repeat rwrtTac_A115; repeat rwrtTac_B115.

Ltac t605 :=
  t_base ||
  List_tactic57 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t606 :=
  t605 ||
  rwrtTac115 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t606.

(***********************
  End of :+
 ***********************)


(***********************
  Start of reverse
 ***********************)


Definition reverse_rt_type (T: Type) (thiss55: List T) : Type :=
{res20: List T | (ifthenelse (Zeq_bool (proj1_sig (size T res20)) (proj1_sig (size T thiss55))) bool
	(fun _ => set_equality (content T res20) (content T thiss55) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold reverse_rt_type.


Equations (noind) reverse (T: Type) (thiss55: List T) : reverse_rt_type T thiss55 := 
	reverse T thiss55 by rec ignore_termination lt :=
	reverse T thiss55 := match thiss55 with
	| Nil_construct _ => thiss55
	| Cons_construct _ x4 xs2 => proj1_sig (snoc_ T (proj1_sig (reverse T xs2)) x4)
	end.

Hint Unfold reverse_comp_proj.

Solve Obligations with (repeat t606).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A116 := match goal with 
	| [ H1348: context[reverse ?T ?thiss55] |- _ ] => 
			poseNew (Mark (T,thiss55) "unfolding reverse_equation")
	| [  |- context[reverse ?T ?thiss55] ] => 
			poseNew (Mark (T,thiss55) "unfolding reverse_equation")
end.

Ltac rwrtTac_B116 := match goal with 
	| [ H1348: context[reverse ?T ?thiss55], H2348: Marked (?T,?thiss55) "unfolding reverse_equation" |- _ ] => 
			poseNew (Mark (T,thiss55) "unfolded reverse_equation");
			add_equation (reverse_equation_1 T thiss55)
	| [ H2348: Marked (?T,?thiss55) "unfolding reverse_equation" |- context[reverse ?T ?thiss55] ] => 
			poseNew (Mark (T,thiss55) "unfolded reverse_equation");
			add_equation (reverse_equation_1 T thiss55)
end.

Ltac rwrtTac116 := rwrtTac115; repeat rwrtTac_A116; repeat rwrtTac_B116.

Ltac t607 :=
  t_base ||
  List_tactic57 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t608 :=
  t607 ||
  rwrtTac116 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t608.

(***********************
  End of reverse
 ***********************)
