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

Ltac t457 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t458 :=
  t457 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t458.


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

Lemma None_exists: (forall T: Type, forall self376: Option T, ((true = isNone T self376)) <-> (((None_construct T = self376)))). 
Proof.
	repeat t458 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self377: Option T, ((true = isSome T self377)) <-> ((exists tmp141: T, (Some_construct T tmp141 = self377)))). 
Proof.
	repeat t458 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic47 := match goal with 
	| [ H188: (true = isNone ?T ?self378) |- _ ] => 
			poseNew (Mark (T,self378) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H188)
	| [ H188: (isNone ?T ?self378 = true) |- _ ] => 
			poseNew (Mark (T,self378) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H188))
	| [ H189: (true = isSome ?T ?self379) |- _ ] => 
			poseNew (Mark (T,self379) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H189)
	| [ H189: (isSome ?T ?self379 = true) |- _ ] => 
			poseNew (Mark (T,self379) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H189))
	| _ => idtac
end.

Ltac t459 :=
  t_base ||
  Option_tactic47 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t460 :=
  t459 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t460.


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

Lemma Cons_exists: (forall T: Type, forall self380: List T, ((true = isCons T self380)) <-> ((exists tmp143: List T, exists tmp142: T, (Cons_construct T tmp142 tmp143 = self380)))). 
Proof.
	repeat t460 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self381: List T, ((true = isNil T self381)) <-> (((Nil_construct T = self381)))). 
Proof.
	repeat t460 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic47 := match goal with 
	| [ H190: (true = isCons ?T ?self382) |- _ ] => 
			poseNew (Mark (T,self382) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H190)
	| [ H190: (isCons ?T ?self382 = true) |- _ ] => 
			poseNew (Mark (T,self382) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H190))
	| [ H191: (true = isNil ?T ?self383) |- _ ] => 
			poseNew (Mark (T,self383) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H191)
	| [ H191: (isNil ?T ?self383 = true) |- _ ] => 
			poseNew (Mark (T,self383) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H191))
	| _ => Option_tactic47
end.

Ltac t461 :=
  t_base ||
  List_tactic47 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t462 :=
  t461 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t462.

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
Definition content_rt20_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt20_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt20_type T thiss1 := 
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

Ltac rwrtTac_A76 := match goal with 
	| [ H1268: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B76 := match goal with 
	| [ H1268: context[content ?T ?thiss1], H2268: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2268: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac76 := idtac; repeat rwrtTac_A76; repeat rwrtTac_B76.

Ltac t463 :=
  t_base ||
  List_tactic47 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t464 :=
  t463 ||
  rwrtTac76 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t464.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt16_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt16_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt16_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A77 := match goal with 
	| [ H1269: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B77 := match goal with 
	| [ H1269: context[size ?T ?thiss30], H2269: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2269: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac77 := rwrtTac76; repeat rwrtTac_A77; repeat rwrtTac_B77.

Ltac t465 :=
  t_base ||
  List_tactic47 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t466 :=
  t465 ||
  rwrtTac77 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t466.

(***********************
  End of size
 ***********************)

(***********************
  Start of ++
 ***********************)

Obligation Tactic:=idtac.
Definition plus_plus__rt3_type (T: Type) (thiss32: List T) (that1: List T) : Type :=
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

Hint Unfold plus_plus__rt3_type.


Equations (noind) plus_plus_ (T: Type) (thiss32: List T) (that1: List T) : plus_plus__rt3_type T thiss32 that1 := 
	plus_plus_ T thiss32 that1 by rec ignore_termination lt :=
	plus_plus_ T thiss32 that1 := match thiss32 with
	| Nil_construct _ => that1
	| Cons_construct _ x2 xs => Cons_construct T x2 (proj1_sig (plus_plus_ T xs that1))
	end.

Hint Unfold plus_plus__comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A78 := match goal with 
	| [ H1270: context[plus_plus_ ?T ?thiss32 ?that1] |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
	| [  |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
end.

Ltac rwrtTac_B78 := match goal with 
	| [ H1270: context[plus_plus_ ?T ?thiss32 ?that1], H2270: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
	| [ H2270: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
end.

Ltac rwrtTac78 := rwrtTac77; repeat rwrtTac_A78; repeat rwrtTac_B78.

Ltac t467 :=
  t_base ||
  List_tactic47 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t468 :=
  t467 ||
  rwrtTac78 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t468.

(***********************
  End of ++
 ***********************)

(***********************
  Start of insertAtImpl
 ***********************)

Obligation Tactic:=idtac.
Definition contractHyp127_type (T: Type) (thiss44: List T) (pos: Z) (l1: List T) : Type :=
(ifthenelse (Z.leb (0)%Z pos) bool
	(fun _ => Z.leb pos (proj1_sig (size T thiss44)) )
	(fun _ => false ) = true).

Fail Next Obligation.

Hint Unfold contractHyp127_type.


Definition insertAtImpl_rt1_type (T: Type) (thiss44: List T) (pos: Z) (l1: List T) (contractHyp127: contractHyp127_type T thiss44 pos l1) : Type :=
{res12: List T | (ifthenelse (Zeq_bool (proj1_sig (size T res12)) (Z.add (proj1_sig (size T thiss44)) (proj1_sig (size T l1)))) bool
	(fun _ => set_equality (content T res12) (set_union (content T thiss44) (content T l1)) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold insertAtImpl_rt1_type.


Equations (noind) insertAtImpl (T: Type) (thiss44: List T) (pos: Z) (l1: List T) (contractHyp127: contractHyp127_type T thiss44 pos l1) : insertAtImpl_rt1_type T thiss44 pos l1 contractHyp127 := 
	insertAtImpl T thiss44 pos l1 contractHyp127 by rec ignore_termination lt :=
	insertAtImpl T thiss44 pos l1 contractHyp127 := ifthenelse (Zeq_bool pos (0)%Z) (List T)
		(fun _ => proj1_sig (plus_plus_ T l1 thiss44) )
		(fun _ => match thiss44 with
		| Cons_construct _ h19 t454 => 
				Cons_construct T h19 (proj1_sig (insertAtImpl T t454 (Z.sub pos (1)%Z) l1 _))
		| Nil_construct _ => l1
		end ).

Hint Unfold insertAtImpl_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A79 := match goal with 
	| [ H1271: context[insertAtImpl ?T ?thiss44 ?pos ?l1] |- _ ] => 
			poseNew (Mark (T,thiss44,pos,l1) "unfolding insertAtImpl_equation")
	| [  |- context[insertAtImpl ?T ?thiss44 ?pos ?l1] ] => 
			poseNew (Mark (T,thiss44,pos,l1) "unfolding insertAtImpl_equation")
end.

Ltac rwrtTac_B79 := match goal with 
	| [ H1271: context[insertAtImpl ?T ?thiss44 ?pos ?l1], H2271: Marked (?T,?thiss44,?pos,?l1) "unfolding insertAtImpl_equation" |- _ ] => 
			poseNew (Mark (T,thiss44,pos,l1) "unfolded insertAtImpl_equation");
			add_equation (insertAtImpl_equation_1 T thiss44 pos l1)
	| [ H2271: Marked (?T,?thiss44,?pos,?l1) "unfolding insertAtImpl_equation" |- context[insertAtImpl ?T ?thiss44 ?pos ?l1] ] => 
			poseNew (Mark (T,thiss44,pos,l1) "unfolded insertAtImpl_equation");
			add_equation (insertAtImpl_equation_1 T thiss44 pos l1)
end.

Ltac rwrtTac79 := rwrtTac78; repeat rwrtTac_A79; repeat rwrtTac_B79.

Ltac t469 :=
  t_base ||
  List_tactic47 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t470 :=
  t469 ||
  rwrtTac79 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t470.

(***********************
  End of insertAtImpl
 ***********************)


(***********************
  Start of insertAt
 ***********************)

Definition insertAt (T: Type) (thiss45: List T) (pos1: Z) (l2: List T) (contractHyp128: (ifthenelse (Z.leb (Z.opp pos1) (proj1_sig (size T thiss45))) bool
	(fun _ => Z.leb pos1 (proj1_sig (size T thiss45)) )
	(fun _ => false ) = true)) : {res13: List T | (ifthenelse (Zeq_bool (proj1_sig (size T res13)) (Z.add (proj1_sig (size T thiss45)) (proj1_sig (size T l2)))) bool
	(fun _ => set_equality (content T res13) (set_union (content T thiss45) (content T l2)) )
	(fun _ => false ) = true)} :=
ifthenelse (Z.ltb pos1 (0)%Z) (List T)
	(fun _ => proj1_sig (insertAtImpl T thiss45 (Z.add (proj1_sig (size T thiss45)) pos1) l2 _) )
	(fun _ => proj1_sig (insertAtImpl T thiss45 pos1 l2 _) ).

Fail Next Obligation.

Hint Unfold insertAt: definitions.

(***********************
  End of insertAt
 ***********************)
