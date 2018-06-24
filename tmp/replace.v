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

Ltac t549 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t550 :=
  t549 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t550.


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

Lemma None_exists: (forall T: Type, forall self432: Option T, ((true = isNone T self432)) <-> (((None_construct T = self432)))). 
Proof.
	repeat t550 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self433: Option T, ((true = isSome T self433)) <-> ((exists tmp162: T, (Some_construct T tmp162 = self433)))). 
Proof.
	repeat t550 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic54 := match goal with 
	| [ H216: (true = isNone ?T ?self434) |- _ ] => 
			poseNew (Mark (T,self434) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H216)
	| [ H216: (isNone ?T ?self434 = true) |- _ ] => 
			poseNew (Mark (T,self434) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H216))
	| [ H217: (true = isSome ?T ?self435) |- _ ] => 
			poseNew (Mark (T,self435) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H217)
	| [ H217: (isSome ?T ?self435 = true) |- _ ] => 
			poseNew (Mark (T,self435) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H217))
	| _ => idtac
end.

Ltac t551 :=
  t_base ||
  Option_tactic54 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t552 :=
  t551 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t552.


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

Lemma Cons_exists: (forall T: Type, forall self436: List T, ((true = isCons T self436)) <-> ((exists tmp164: List T, exists tmp163: T, (Cons_construct T tmp163 tmp164 = self436)))). 
Proof.
	repeat t552 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self437: List T, ((true = isNil T self437)) <-> (((Nil_construct T = self437)))). 
Proof.
	repeat t552 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic54 := match goal with 
	| [ H218: (true = isCons ?T ?self438) |- _ ] => 
			poseNew (Mark (T,self438) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H218)
	| [ H218: (isCons ?T ?self438 = true) |- _ ] => 
			poseNew (Mark (T,self438) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H218))
	| [ H219: (true = isNil ?T ?self439) |- _ ] => 
			poseNew (Mark (T,self439) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H219)
	| [ H219: (isNil ?T ?self439 = true) |- _ ] => 
			poseNew (Mark (T,self439) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H219))
	| _ => Option_tactic54
end.

Ltac t553 :=
  t_base ||
  List_tactic54 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t554 :=
  t553 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t554.

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
Definition content_rt25_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt25_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt25_type T thiss1 := 
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

Ltac rwrtTac_A100 := match goal with 
	| [ H1320: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B100 := match goal with 
	| [ H1320: context[content ?T ?thiss1], H2320: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2320: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac100 := idtac; repeat rwrtTac_A100; repeat rwrtTac_B100.

Ltac t555 :=
  t_base ||
  List_tactic54 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t556 :=
  t555 ||
  rwrtTac100 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t556.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt23_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt23_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt23_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A101 := match goal with 
	| [ H1321: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B101 := match goal with 
	| [ H1321: context[size ?T ?thiss30], H2321: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2321: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac101 := rwrtTac100; repeat rwrtTac_A101; repeat rwrtTac_B101.

Ltac t557 :=
  t_base ||
  List_tactic54 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t558 :=
  t557 ||
  rwrtTac101 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t558.

(***********************
  End of size
 ***********************)


(***********************
  Start of replace
 ***********************)


Definition replace_rt_type (T: Type) (thiss52: List T) (from: T) (to: T) : Type :=
{res17: List T | (ifthenelse (Zeq_bool (proj1_sig (size T res17)) (proj1_sig (size T thiss52))) bool
	(fun _ => set_equality (content T res17) (set_union (set_difference (content T thiss52) (set_union (@set_empty T) (set_singleton from))) (ifthenelse (set_elem_of from (content T thiss52)) (set (T))
		(fun _ => set_union (@set_empty T) (set_singleton to) )
		(fun _ => @set_empty T ))) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold replace_rt_type.


Equations (noind) replace (T: Type) (thiss52: List T) (from: T) (to: T) : replace_rt_type T thiss52 from to := 
	replace T thiss52 from to by rec ignore_termination lt :=
	replace T thiss52 from to := match thiss52 with
	| Nil_construct _ => Nil_construct T
	| Cons_construct _ h22 t559 => 
			let r2 := (proj1_sig (replace T t559 from to)) in (ifthenelse (propInBool ((h22 = from))) (List T)
				(fun _ => Cons_construct T to r2 )
				(fun _ => Cons_construct T h22 r2 ))
	end.

Hint Unfold replace_comp_proj.

Solve Obligations with (repeat t558).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A102 := match goal with 
	| [ H1322: context[replace ?T ?thiss52 ?from ?to] |- _ ] => 
			poseNew (Mark (T,thiss52,from,to) "unfolding replace_equation")
	| [  |- context[replace ?T ?thiss52 ?from ?to] ] => 
			poseNew (Mark (T,thiss52,from,to) "unfolding replace_equation")
end.

Ltac rwrtTac_B102 := match goal with 
	| [ H1322: context[replace ?T ?thiss52 ?from ?to], H2322: Marked (?T,?thiss52,?from,?to) "unfolding replace_equation" |- _ ] => 
			poseNew (Mark (T,thiss52,from,to) "unfolded replace_equation");
			add_equation (replace_equation_1 T thiss52 from to)
	| [ H2322: Marked (?T,?thiss52,?from,?to) "unfolding replace_equation" |- context[replace ?T ?thiss52 ?from ?to] ] => 
			poseNew (Mark (T,thiss52,from,to) "unfolded replace_equation");
			add_equation (replace_equation_1 T thiss52 from to)
end.

Ltac rwrtTac102 := rwrtTac101; repeat rwrtTac_A102; repeat rwrtTac_B102.

Ltac t560 :=
  t_base ||
  List_tactic54 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t561 :=
  t560 ||
  rwrtTac102 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t561.

(***********************
  End of replace
 ***********************)
