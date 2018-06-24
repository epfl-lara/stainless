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

Ltac t471 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t472 :=
  t471 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t472.


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

Lemma None_exists: (forall T: Type, forall self384: Option T, ((true = isNone T self384)) <-> (((None_construct T = self384)))). 
Proof.
	repeat t472 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self385: Option T, ((true = isSome T self385)) <-> ((exists tmp144: T, (Some_construct T tmp144 = self385)))). 
Proof.
	repeat t472 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic48 := match goal with 
	| [ H192: (true = isNone ?T ?self386) |- _ ] => 
			poseNew (Mark (T,self386) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H192)
	| [ H192: (isNone ?T ?self386 = true) |- _ ] => 
			poseNew (Mark (T,self386) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H192))
	| [ H193: (true = isSome ?T ?self387) |- _ ] => 
			poseNew (Mark (T,self387) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H193)
	| [ H193: (isSome ?T ?self387 = true) |- _ ] => 
			poseNew (Mark (T,self387) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H193))
	| _ => idtac
end.

Ltac t473 :=
  t_base ||
  Option_tactic48 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t474 :=
  t473 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t474.


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

Lemma Cons_exists: (forall T: Type, forall self388: List T, ((true = isCons T self388)) <-> ((exists tmp146: List T, exists tmp145: T, (Cons_construct T tmp145 tmp146 = self388)))). 
Proof.
	repeat t474 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self389: List T, ((true = isNil T self389)) <-> (((Nil_construct T = self389)))). 
Proof.
	repeat t474 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic48 := match goal with 
	| [ H194: (true = isCons ?T ?self390) |- _ ] => 
			poseNew (Mark (T,self390) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H194)
	| [ H194: (isCons ?T ?self390 = true) |- _ ] => 
			poseNew (Mark (T,self390) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H194))
	| [ H195: (true = isNil ?T ?self391) |- _ ] => 
			poseNew (Mark (T,self391) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H195)
	| [ H195: (isNil ?T ?self391 = true) |- _ ] => 
			poseNew (Mark (T,self391) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H195))
	| _ => Option_tactic48
end.

Ltac t475 :=
  t_base ||
  List_tactic48 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t476 :=
  t475 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t476.

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
Definition content_rt21_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt21_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt21_type T thiss1 := 
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

Ltac rwrtTac_A80 := match goal with 
	| [ H1276: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B80 := match goal with 
	| [ H1276: context[content ?T ?thiss1], H2276: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2276: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac80 := idtac; repeat rwrtTac_A80; repeat rwrtTac_B80.

Ltac t477 :=
  t_base ||
  List_tactic48 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t478 :=
  t477 ||
  rwrtTac80 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t478.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt17_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt17_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt17_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A81 := match goal with 
	| [ H1277: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B81 := match goal with 
	| [ H1277: context[size ?T ?thiss30], H2277: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2277: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac81 := rwrtTac80; repeat rwrtTac_A81; repeat rwrtTac_B81.

Ltac t479 :=
  t_base ||
  List_tactic48 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t480 :=
  t479 ||
  rwrtTac81 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t480.

(***********************
  End of size
 ***********************)

(***********************
  Start of ++
 ***********************)

Obligation Tactic:=idtac.
Definition plus_plus__rt4_type (T: Type) (thiss32: List T) (that1: List T) : Type :=
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

Hint Unfold plus_plus__rt4_type.


Equations (noind) plus_plus_ (T: Type) (thiss32: List T) (that1: List T) : plus_plus__rt4_type T thiss32 that1 := 
	plus_plus_ T thiss32 that1 by rec ignore_termination lt :=
	plus_plus_ T thiss32 that1 := match thiss32 with
	| Nil_construct _ => that1
	| Cons_construct _ x2 xs => Cons_construct T x2 (proj1_sig (plus_plus_ T xs that1))
	end.

Hint Unfold plus_plus__comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A82 := match goal with 
	| [ H1278: context[plus_plus_ ?T ?thiss32 ?that1] |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
	| [  |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
end.

Ltac rwrtTac_B82 := match goal with 
	| [ H1278: context[plus_plus_ ?T ?thiss32 ?that1], H2278: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
	| [ H2278: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
end.

Ltac rwrtTac82 := rwrtTac81; repeat rwrtTac_A82; repeat rwrtTac_B82.

Ltac t481 :=
  t_base ||
  List_tactic48 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t482 :=
  t481 ||
  rwrtTac82 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t482.

(***********************
  End of ++
 ***********************)

(***********************
  Start of insertAtImpl
 ***********************)

Obligation Tactic:=idtac.
Definition contractHyp132_type (T: Type) (thiss44: List T) (pos: Z) (l1: List T) : Type :=
(ifthenelse (Z.leb (0)%Z pos) bool
	(fun _ => Z.leb pos (proj1_sig (size T thiss44)) )
	(fun _ => false ) = true).

Fail Next Obligation.

Hint Unfold contractHyp132_type.


Definition insertAtImpl_rt2_type (T: Type) (thiss44: List T) (pos: Z) (l1: List T) (contractHyp132: contractHyp132_type T thiss44 pos l1) : Type :=
{res12: List T | (ifthenelse (Zeq_bool (proj1_sig (size T res12)) (Z.add (proj1_sig (size T thiss44)) (proj1_sig (size T l1)))) bool
	(fun _ => set_equality (content T res12) (set_union (content T thiss44) (content T l1)) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold insertAtImpl_rt2_type.


Equations (noind) insertAtImpl (T: Type) (thiss44: List T) (pos: Z) (l1: List T) (contractHyp132: contractHyp132_type T thiss44 pos l1) : insertAtImpl_rt2_type T thiss44 pos l1 contractHyp132 := 
	insertAtImpl T thiss44 pos l1 contractHyp132 by rec ignore_termination lt :=
	insertAtImpl T thiss44 pos l1 contractHyp132 := ifthenelse (Zeq_bool pos (0)%Z) (List T)
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

Ltac rwrtTac_A83 := match goal with 
	| [ H1279: context[insertAtImpl ?T ?thiss44 ?pos ?l1] |- _ ] => 
			poseNew (Mark (T,thiss44,pos,l1) "unfolding insertAtImpl_equation")
	| [  |- context[insertAtImpl ?T ?thiss44 ?pos ?l1] ] => 
			poseNew (Mark (T,thiss44,pos,l1) "unfolding insertAtImpl_equation")
end.

Ltac rwrtTac_B83 := match goal with 
	| [ H1279: context[insertAtImpl ?T ?thiss44 ?pos ?l1], H2279: Marked (?T,?thiss44,?pos,?l1) "unfolding insertAtImpl_equation" |- _ ] => 
			poseNew (Mark (T,thiss44,pos,l1) "unfolded insertAtImpl_equation");
			add_equation (insertAtImpl_equation_1 T thiss44 pos l1)
	| [ H2279: Marked (?T,?thiss44,?pos,?l1) "unfolding insertAtImpl_equation" |- context[insertAtImpl ?T ?thiss44 ?pos ?l1] ] => 
			poseNew (Mark (T,thiss44,pos,l1) "unfolded insertAtImpl_equation");
			add_equation (insertAtImpl_equation_1 T thiss44 pos l1)
end.

Ltac rwrtTac83 := rwrtTac82; repeat rwrtTac_A83; repeat rwrtTac_B83.

Ltac t483 :=
  t_base ||
  List_tactic48 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t484 :=
  t483 ||
  rwrtTac83 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t484.

(***********************
  End of insertAtImpl
 ***********************)

(***********************
  Start of insertAt
 ***********************)

Definition insertAt (T: Type) (thiss45: List T) (pos1: Z) (l2: List T) (contractHyp133: (ifthenelse (Z.leb (Z.opp pos1) (proj1_sig (size T thiss45))) bool
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


(***********************
  Start of insertAt
 ***********************)

Definition insertAt1 (T: Type) (thiss46: List T) (pos2: Z) (e1: T) (contractHyp134: (ifthenelse (Z.leb (Z.opp pos2) (proj1_sig (size T thiss46))) bool
	(fun _ => Z.leb pos2 (proj1_sig (size T thiss46)) )
	(fun _ => false ) = true)) : {res14: List T | (ifthenelse (Zeq_bool (proj1_sig (size T res14)) (Z.add (proj1_sig (size T thiss46)) (1)%Z)) bool
	(fun _ => set_equality (content T res14) (set_union (content T thiss46) (set_union (@set_empty T) (set_singleton e1))) )
	(fun _ => false ) = true)} :=
proj1_sig (insertAt T thiss46 pos2 (Cons_construct T e1 (Nil_construct T)) _).

Fail Next Obligation.

Hint Unfold insertAt1: definitions.

(***********************
  End of insertAt
 ***********************)
