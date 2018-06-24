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

Ltac t442 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t443 :=
  t442 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t443.


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

Lemma None_exists: (forall T: Type, forall self368: Option T, ((true = isNone T self368)) <-> (((None_construct T = self368)))). 
Proof.
	repeat t443 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self369: Option T, ((true = isSome T self369)) <-> ((exists tmp138: T, (Some_construct T tmp138 = self369)))). 
Proof.
	repeat t443 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic46 := match goal with 
	| [ H184: (true = isNone ?T ?self370) |- _ ] => 
			poseNew (Mark (T,self370) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H184)
	| [ H184: (isNone ?T ?self370 = true) |- _ ] => 
			poseNew (Mark (T,self370) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H184))
	| [ H185: (true = isSome ?T ?self371) |- _ ] => 
			poseNew (Mark (T,self371) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H185)
	| [ H185: (isSome ?T ?self371 = true) |- _ ] => 
			poseNew (Mark (T,self371) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H185))
	| _ => idtac
end.

Ltac t444 :=
  t_base ||
  Option_tactic46 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t445 :=
  t444 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t445.


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

Lemma Cons_exists: (forall T: Type, forall self372: List T, ((true = isCons T self372)) <-> ((exists tmp140: List T, exists tmp139: T, (Cons_construct T tmp139 tmp140 = self372)))). 
Proof.
	repeat t445 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self373: List T, ((true = isNil T self373)) <-> (((Nil_construct T = self373)))). 
Proof.
	repeat t445 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic46 := match goal with 
	| [ H186: (true = isCons ?T ?self374) |- _ ] => 
			poseNew (Mark (T,self374) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H186)
	| [ H186: (isCons ?T ?self374 = true) |- _ ] => 
			poseNew (Mark (T,self374) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H186))
	| [ H187: (true = isNil ?T ?self375) |- _ ] => 
			poseNew (Mark (T,self375) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H187)
	| [ H187: (isNil ?T ?self375 = true) |- _ ] => 
			poseNew (Mark (T,self375) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H187))
	| _ => Option_tactic46
end.

Ltac t446 :=
  t_base ||
  List_tactic46 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t447 :=
  t446 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t447.

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
Definition content_rt19_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt19_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt19_type T thiss1 := 
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

Ltac rwrtTac_A72 := match goal with 
	| [ H1260: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B72 := match goal with 
	| [ H1260: context[content ?T ?thiss1], H2260: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2260: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac72 := idtac; repeat rwrtTac_A72; repeat rwrtTac_B72.

Ltac t448 :=
  t_base ||
  List_tactic46 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t449 :=
  t448 ||
  rwrtTac72 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t449.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt15_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt15_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt15_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A73 := match goal with 
	| [ H1261: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B73 := match goal with 
	| [ H1261: context[size ?T ?thiss30], H2261: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2261: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac73 := rwrtTac72; repeat rwrtTac_A73; repeat rwrtTac_B73.

Ltac t450 :=
  t_base ||
  List_tactic46 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t451 :=
  t450 ||
  rwrtTac73 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t451.

(***********************
  End of size
 ***********************)

(***********************
  Start of ++
 ***********************)

Obligation Tactic:=idtac.
Definition plus_plus__rt2_type (T: Type) (thiss32: List T) (that1: List T) : Type :=
{res3: List T | (ifthenelse
	(ifthenelse (set_equality (content T res3) (set_union (content T thiss32) (content T that1))) bool
		(fun _ => Zeq_bool (proj1_sig (size T res3)) (Z.add (proj1_sig (size T thiss32)) (proj1_sig (size T that1))) )
		(fun _ => false ))
	bool
	(fun _ => ifthenelse (negb (propInBool ((that1 = Nil_construct T)))) bool
		(fun _ => true )
		(fun _ => propInBool ((res3 = thiss32)) ) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold plus_plus__rt2_type.


Equations (noind) plus_plus_ (T: Type) (thiss32: List T) (that1: List T) : plus_plus__rt2_type T thiss32 that1 := 
	plus_plus_ T thiss32 that1 by rec ignore_termination lt :=
	plus_plus_ T thiss32 that1 := match thiss32 with
	| Nil_construct _ => that1
	| Cons_construct _ x2 xs => Cons_construct T x2 (proj1_sig (plus_plus_ T xs that1))
	end.

Hint Unfold plus_plus__comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A74 := match goal with 
	| [ H1262: context[plus_plus_ ?T ?thiss32 ?that1] |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
	| [  |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
end.

Ltac rwrtTac_B74 := match goal with 
	| [ H1262: context[plus_plus_ ?T ?thiss32 ?that1], H2262: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
	| [ H2262: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
end.

Ltac rwrtTac74 := rwrtTac73; repeat rwrtTac_A74; repeat rwrtTac_B74.

Ltac t452 :=
  t_base ||
  List_tactic46 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t453 :=
  t452 ||
  rwrtTac74 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t453.

(***********************
  End of ++
 ***********************)


(***********************
  Start of insertAtImpl
 ***********************)


Definition contractHyp123_type (T: Type) (thiss44: List T) (pos: Z) (l1: List T) : Type :=
(ifthenelse (Z.leb (0)%Z pos) bool
	(fun _ => Z.leb pos (proj1_sig (size T thiss44)) )
	(fun _ => false ) = true).

Fail Next Obligation.

Hint Unfold contractHyp123_type.


Definition insertAtImpl_rt_type (T: Type) (thiss44: List T) (pos: Z) (l1: List T) (contractHyp123: contractHyp123_type T thiss44 pos l1) : Type :=
{res12: List T | (ifthenelse (Zeq_bool (proj1_sig (size T res12)) (Z.add (proj1_sig (size T thiss44)) (proj1_sig (size T l1)))) bool
	(fun _ => set_equality (content T res12) (set_union (content T thiss44) (content T l1)) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold insertAtImpl_rt_type.


Equations (noind) insertAtImpl (T: Type) (thiss44: List T) (pos: Z) (l1: List T) (contractHyp123: contractHyp123_type T thiss44 pos l1) : insertAtImpl_rt_type T thiss44 pos l1 contractHyp123 := 
	insertAtImpl T thiss44 pos l1 contractHyp123 by rec ignore_termination lt :=
	insertAtImpl T thiss44 pos l1 contractHyp123 := ifthenelse (Zeq_bool pos (0)%Z) (List T)
		(fun _ => proj1_sig (plus_plus_ T l1 thiss44) )
		(fun _ => match thiss44 with
		| Cons_construct _ h19 t454 => 
				Cons_construct T h19 (proj1_sig (insertAtImpl T t454 (Z.sub pos (1)%Z) l1 _))
		| Nil_construct _ => l1
		end ).

Hint Unfold insertAtImpl_comp_proj.

Solve Obligations with (repeat t453).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A75 := match goal with 
	| [ H1263: context[insertAtImpl ?T ?thiss44 ?pos ?l1] |- _ ] => 
			poseNew (Mark (T,thiss44,pos,l1) "unfolding insertAtImpl_equation")
	| [  |- context[insertAtImpl ?T ?thiss44 ?pos ?l1] ] => 
			poseNew (Mark (T,thiss44,pos,l1) "unfolding insertAtImpl_equation")
end.

Ltac rwrtTac_B75 := match goal with 
	| [ H1263: context[insertAtImpl ?T ?thiss44 ?pos ?l1], H2263: Marked (?T,?thiss44,?pos,?l1) "unfolding insertAtImpl_equation" |- _ ] => 
			poseNew (Mark (T,thiss44,pos,l1) "unfolded insertAtImpl_equation");
			add_equation (insertAtImpl_equation_1 T thiss44 pos l1)
	| [ H2263: Marked (?T,?thiss44,?pos,?l1) "unfolding insertAtImpl_equation" |- context[insertAtImpl ?T ?thiss44 ?pos ?l1] ] => 
			poseNew (Mark (T,thiss44,pos,l1) "unfolded insertAtImpl_equation");
			add_equation (insertAtImpl_equation_1 T thiss44 pos l1)
end.

Ltac rwrtTac75 := rwrtTac74; repeat rwrtTac_A75; repeat rwrtTac_B75.

Ltac t455 :=
  t_base ||
  List_tactic46 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t456 :=
  t455 ||
  rwrtTac75 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t456.

(***********************
  End of insertAtImpl
 ***********************)
