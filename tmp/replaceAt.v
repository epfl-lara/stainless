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

Ltac t579 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t580 :=
  t579 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t580.


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

Lemma None_exists: (forall T: Type, forall self448: Option T, ((true = isNone T self448)) <-> (((None_construct T = self448)))). 
Proof.
	repeat t580 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self449: Option T, ((true = isSome T self449)) <-> ((exists tmp168: T, (Some_construct T tmp168 = self449)))). 
Proof.
	repeat t580 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic56 := match goal with 
	| [ H224: (true = isNone ?T ?self450) |- _ ] => 
			poseNew (Mark (T,self450) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H224)
	| [ H224: (isNone ?T ?self450 = true) |- _ ] => 
			poseNew (Mark (T,self450) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H224))
	| [ H225: (true = isSome ?T ?self451) |- _ ] => 
			poseNew (Mark (T,self451) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H225)
	| [ H225: (isSome ?T ?self451 = true) |- _ ] => 
			poseNew (Mark (T,self451) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H225))
	| _ => idtac
end.

Ltac t581 :=
  t_base ||
  Option_tactic56 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t582 :=
  t581 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t582.


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

Lemma Cons_exists: (forall T: Type, forall self452: List T, ((true = isCons T self452)) <-> ((exists tmp170: List T, exists tmp169: T, (Cons_construct T tmp169 tmp170 = self452)))). 
Proof.
	repeat t582 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self453: List T, ((true = isNil T self453)) <-> (((Nil_construct T = self453)))). 
Proof.
	repeat t582 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic56 := match goal with 
	| [ H226: (true = isCons ?T ?self454) |- _ ] => 
			poseNew (Mark (T,self454) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H226)
	| [ H226: (isCons ?T ?self454 = true) |- _ ] => 
			poseNew (Mark (T,self454) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H226))
	| [ H227: (true = isNil ?T ?self455) |- _ ] => 
			poseNew (Mark (T,self455) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H227)
	| [ H227: (isNil ?T ?self455 = true) |- _ ] => 
			poseNew (Mark (T,self455) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H227))
	| _ => Option_tactic56
end.

Ltac t583 :=
  t_base ||
  List_tactic56 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t584 :=
  t583 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t584.

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
Definition content_rt27_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt27_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt27_type T thiss1 := 
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

Ltac rwrtTac_A108 := match goal with 
	| [ H1336: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B108 := match goal with 
	| [ H1336: context[content ?T ?thiss1], H2336: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2336: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac108 := idtac; repeat rwrtTac_A108; repeat rwrtTac_B108.

Ltac t585 :=
  t_base ||
  List_tactic56 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t586 :=
  t585 ||
  rwrtTac108 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t586.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt25_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt25_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt25_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A109 := match goal with 
	| [ H1337: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B109 := match goal with 
	| [ H1337: context[size ?T ?thiss30], H2337: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2337: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac109 := rwrtTac108; repeat rwrtTac_A109; repeat rwrtTac_B109.

Ltac t587 :=
  t_base ||
  List_tactic56 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t588 :=
  t587 ||
  rwrtTac109 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t588.

(***********************
  End of size
 ***********************)

(***********************
  Start of ++
 ***********************)

Obligation Tactic:=idtac.
Definition plus_plus__rt7_type (T: Type) (thiss32: List T) (that1: List T) : Type :=
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

Hint Unfold plus_plus__rt7_type.


Equations (noind) plus_plus_ (T: Type) (thiss32: List T) (that1: List T) : plus_plus__rt7_type T thiss32 that1 := 
	plus_plus_ T thiss32 that1 by rec ignore_termination lt :=
	plus_plus_ T thiss32 that1 := match thiss32 with
	| Nil_construct _ => that1
	| Cons_construct _ x2 xs => Cons_construct T x2 (proj1_sig (plus_plus_ T xs that1))
	end.

Hint Unfold plus_plus__comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A110 := match goal with 
	| [ H1338: context[plus_plus_ ?T ?thiss32 ?that1] |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
	| [  |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
end.

Ltac rwrtTac_B110 := match goal with 
	| [ H1338: context[plus_plus_ ?T ?thiss32 ?that1], H2338: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
	| [ H2338: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
end.

Ltac rwrtTac110 := rwrtTac109; repeat rwrtTac_A110; repeat rwrtTac_B110.

Ltac t589 :=
  t_base ||
  List_tactic56 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t590 :=
  t589 ||
  rwrtTac110 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t590.

(***********************
  End of ++
 ***********************)

(***********************
  Start of drop
 ***********************)

Obligation Tactic:=idtac.
Definition drop_rt2_type (T: Type) (thiss38: List T) (i: Z) : Type :=
{res8: List T | (ifthenelse (set_subset (content T res8) (content T thiss38)) bool
	(fun _ => Zeq_bool (proj1_sig (size T res8)) (ifthenelse (Z.leb i (0)%Z) Z
		(fun _ => proj1_sig (size T thiss38) )
		(fun _ => ifthenelse (Z.geb i (proj1_sig (size T thiss38))) Z
			(fun _ => (0)%Z )
			(fun _ => Z.sub (proj1_sig (size T thiss38)) i ) )) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold drop_rt2_type.


Equations (noind) drop (T: Type) (thiss38: List T) (i: Z) : drop_rt2_type T thiss38 i := 
	drop T thiss38 i by rec ignore_termination lt :=
	drop T thiss38 i := ifthenelse (isNil _ thiss38) (List T)
		(fun _ => Nil_construct T )
		(fun _ => ifthenelse (isCons _ thiss38) (List T)
			(fun _ => ifthenelse (Z.leb i (0)%Z) (List T)
				(fun _ => Cons_construct T (h T thiss38) (t7 T thiss38) )
				(fun _ => proj1_sig (drop T (t7 T thiss38) (Z.sub i (1)%Z)) ) )
			(fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold drop_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A111 := match goal with 
	| [ H1339: context[drop ?T ?thiss38 ?i] |- _ ] => 
			poseNew (Mark (T,thiss38,i) "unfolding drop_equation")
	| [  |- context[drop ?T ?thiss38 ?i] ] => 
			poseNew (Mark (T,thiss38,i) "unfolding drop_equation")
end.

Ltac rwrtTac_B111 := match goal with 
	| [ H1339: context[drop ?T ?thiss38 ?i], H2339: Marked (?T,?thiss38,?i) "unfolding drop_equation" |- _ ] => 
			poseNew (Mark (T,thiss38,i) "unfolded drop_equation");
			add_equation (drop_equation_1 T thiss38 i)
	| [ H2339: Marked (?T,?thiss38,?i) "unfolding drop_equation" |- context[drop ?T ?thiss38 ?i] ] => 
			poseNew (Mark (T,thiss38,i) "unfolded drop_equation");
			add_equation (drop_equation_1 T thiss38 i)
end.

Ltac rwrtTac111 := rwrtTac110; repeat rwrtTac_A111; repeat rwrtTac_B111.

Ltac t591 :=
  t_base ||
  List_tactic56 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t592 :=
  t591 ||
  rwrtTac111 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t592.

(***********************
  End of drop
 ***********************)

(***********************
  Start of replaceAtImpl
 ***********************)

Obligation Tactic:=idtac.
Definition contractHyp169_type (T: Type) (thiss53: List T) (pos3: Z) (l3: List T) : Type :=
(ifthenelse (Z.leb (0)%Z pos3) bool
	(fun _ => Z.leb pos3 (proj1_sig (size T thiss53)) )
	(fun _ => false ) = true).

Fail Next Obligation.

Hint Unfold contractHyp169_type.


Definition replaceAtImpl_rt1_type (T: Type) (thiss53: List T) (pos3: Z) (l3: List T) (contractHyp169: contractHyp169_type T thiss53 pos3 l3) : Type :=
{res18: List T | (set_subset (content T res18) (set_union (content T l3) (content T thiss53)) = true)}.

Fail Next Obligation.

Hint Unfold replaceAtImpl_rt1_type.


Equations (noind) replaceAtImpl (T: Type) (thiss53: List T) (pos3: Z) (l3: List T) (contractHyp169: contractHyp169_type T thiss53 pos3 l3) : replaceAtImpl_rt1_type T thiss53 pos3 l3 contractHyp169 := 
	replaceAtImpl T thiss53 pos3 l3 contractHyp169 by rec ignore_termination lt :=
	replaceAtImpl T thiss53 pos3 l3 contractHyp169 := ifthenelse (Zeq_bool pos3 (0)%Z) (List T)
		(fun _ => proj1_sig (plus_plus_ T l3 (proj1_sig (drop T thiss53 (proj1_sig (size T l3))))) )
		(fun _ => match thiss53 with
		| Cons_construct _ h23 t576 => 
				Cons_construct T h23 (proj1_sig (replaceAtImpl T t576 (Z.sub pos3 (1)%Z) l3 _))
		| Nil_construct _ => l3
		end ).

Hint Unfold replaceAtImpl_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A112 := match goal with 
	| [ H1340: context[replaceAtImpl ?T ?thiss53 ?pos3 ?l3] |- _ ] => 
			poseNew (Mark (T,thiss53,pos3,l3) "unfolding replaceAtImpl_equation")
	| [  |- context[replaceAtImpl ?T ?thiss53 ?pos3 ?l3] ] => 
			poseNew (Mark (T,thiss53,pos3,l3) "unfolding replaceAtImpl_equation")
end.

Ltac rwrtTac_B112 := match goal with 
	| [ H1340: context[replaceAtImpl ?T ?thiss53 ?pos3 ?l3], H2340: Marked (?T,?thiss53,?pos3,?l3) "unfolding replaceAtImpl_equation" |- _ ] => 
			poseNew (Mark (T,thiss53,pos3,l3) "unfolded replaceAtImpl_equation");
			add_equation (replaceAtImpl_equation_1 T thiss53 pos3 l3)
	| [ H2340: Marked (?T,?thiss53,?pos3,?l3) "unfolding replaceAtImpl_equation" |- context[replaceAtImpl ?T ?thiss53 ?pos3 ?l3] ] => 
			poseNew (Mark (T,thiss53,pos3,l3) "unfolded replaceAtImpl_equation");
			add_equation (replaceAtImpl_equation_1 T thiss53 pos3 l3)
end.

Ltac rwrtTac112 := rwrtTac111; repeat rwrtTac_A112; repeat rwrtTac_B112.

Ltac t593 :=
  t_base ||
  List_tactic56 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t594 :=
  t593 ||
  rwrtTac112 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t594.

(***********************
  End of replaceAtImpl
 ***********************)


(***********************
  Start of replaceAt
 ***********************)

Definition replaceAt (T: Type) (thiss54: List T) (pos4: Z) (l4: List T) (contractHyp170: (ifthenelse (Z.leb (Z.opp pos4) (proj1_sig (size T thiss54))) bool
	(fun _ => Z.leb pos4 (proj1_sig (size T thiss54)) )
	(fun _ => false ) = true)) : {res19: List T | (set_subset (content T res19) (set_union (content T l4) (content T thiss54)) = true)} :=
ifthenelse (Z.ltb pos4 (0)%Z) (List T)
	(fun _ => proj1_sig (replaceAtImpl T thiss54 (Z.add (proj1_sig (size T thiss54)) pos4) l4 _) )
	(fun _ => proj1_sig (replaceAtImpl T thiss54 pos4 l4 _) ).

Fail Next Obligation.

Hint Unfold replaceAt: definitions.

(***********************
  End of replaceAt
 ***********************)
