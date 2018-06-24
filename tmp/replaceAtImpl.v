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

Ltac t562 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t563 :=
  t562 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t563.


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

Lemma None_exists: (forall T: Type, forall self440: Option T, ((true = isNone T self440)) <-> (((None_construct T = self440)))). 
Proof.
	repeat t563 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self441: Option T, ((true = isSome T self441)) <-> ((exists tmp165: T, (Some_construct T tmp165 = self441)))). 
Proof.
	repeat t563 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic55 := match goal with 
	| [ H220: (true = isNone ?T ?self442) |- _ ] => 
			poseNew (Mark (T,self442) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H220)
	| [ H220: (isNone ?T ?self442 = true) |- _ ] => 
			poseNew (Mark (T,self442) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H220))
	| [ H221: (true = isSome ?T ?self443) |- _ ] => 
			poseNew (Mark (T,self443) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H221)
	| [ H221: (isSome ?T ?self443 = true) |- _ ] => 
			poseNew (Mark (T,self443) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H221))
	| _ => idtac
end.

Ltac t564 :=
  t_base ||
  Option_tactic55 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t565 :=
  t564 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t565.


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

Lemma Cons_exists: (forall T: Type, forall self444: List T, ((true = isCons T self444)) <-> ((exists tmp167: List T, exists tmp166: T, (Cons_construct T tmp166 tmp167 = self444)))). 
Proof.
	repeat t565 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self445: List T, ((true = isNil T self445)) <-> (((Nil_construct T = self445)))). 
Proof.
	repeat t565 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic55 := match goal with 
	| [ H222: (true = isCons ?T ?self446) |- _ ] => 
			poseNew (Mark (T,self446) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H222)
	| [ H222: (isCons ?T ?self446 = true) |- _ ] => 
			poseNew (Mark (T,self446) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H222))
	| [ H223: (true = isNil ?T ?self447) |- _ ] => 
			poseNew (Mark (T,self447) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H223)
	| [ H223: (isNil ?T ?self447 = true) |- _ ] => 
			poseNew (Mark (T,self447) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H223))
	| _ => Option_tactic55
end.

Ltac t566 :=
  t_base ||
  List_tactic55 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t567 :=
  t566 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t567.

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
Definition content_rt26_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt26_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt26_type T thiss1 := 
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

Ltac rwrtTac_A103 := match goal with 
	| [ H1327: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B103 := match goal with 
	| [ H1327: context[content ?T ?thiss1], H2327: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2327: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac103 := idtac; repeat rwrtTac_A103; repeat rwrtTac_B103.

Ltac t568 :=
  t_base ||
  List_tactic55 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t569 :=
  t568 ||
  rwrtTac103 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t569.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt24_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt24_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt24_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A104 := match goal with 
	| [ H1328: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B104 := match goal with 
	| [ H1328: context[size ?T ?thiss30], H2328: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2328: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac104 := rwrtTac103; repeat rwrtTac_A104; repeat rwrtTac_B104.

Ltac t570 :=
  t_base ||
  List_tactic55 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t571 :=
  t570 ||
  rwrtTac104 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t571.

(***********************
  End of size
 ***********************)

(***********************
  Start of ++
 ***********************)

Obligation Tactic:=idtac.
Definition plus_plus__rt6_type (T: Type) (thiss32: List T) (that1: List T) : Type :=
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

Hint Unfold plus_plus__rt6_type.


Equations (noind) plus_plus_ (T: Type) (thiss32: List T) (that1: List T) : plus_plus__rt6_type T thiss32 that1 := 
	plus_plus_ T thiss32 that1 by rec ignore_termination lt :=
	plus_plus_ T thiss32 that1 := match thiss32 with
	| Nil_construct _ => that1
	| Cons_construct _ x2 xs => Cons_construct T x2 (proj1_sig (plus_plus_ T xs that1))
	end.

Hint Unfold plus_plus__comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A105 := match goal with 
	| [ H1329: context[plus_plus_ ?T ?thiss32 ?that1] |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
	| [  |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
end.

Ltac rwrtTac_B105 := match goal with 
	| [ H1329: context[plus_plus_ ?T ?thiss32 ?that1], H2329: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
	| [ H2329: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
end.

Ltac rwrtTac105 := rwrtTac104; repeat rwrtTac_A105; repeat rwrtTac_B105.

Ltac t572 :=
  t_base ||
  List_tactic55 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t573 :=
  t572 ||
  rwrtTac105 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t573.

(***********************
  End of ++
 ***********************)

(***********************
  Start of drop
 ***********************)

Obligation Tactic:=idtac.
Definition drop_rt1_type (T: Type) (thiss38: List T) (i: Z) : Type :=
{res8: List T | (ifthenelse (set_subset (content T res8) (content T thiss38)) bool
	(fun _ => Zeq_bool (proj1_sig (size T res8)) (ifthenelse (Z.leb i (0)%Z) Z
		(fun _ => proj1_sig (size T thiss38) )
		(fun _ => ifthenelse (Z.geb i (proj1_sig (size T thiss38))) Z
			(fun _ => (0)%Z )
			(fun _ => Z.sub (proj1_sig (size T thiss38)) i ) )) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold drop_rt1_type.


Equations (noind) drop (T: Type) (thiss38: List T) (i: Z) : drop_rt1_type T thiss38 i := 
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

Ltac rwrtTac_A106 := match goal with 
	| [ H1330: context[drop ?T ?thiss38 ?i] |- _ ] => 
			poseNew (Mark (T,thiss38,i) "unfolding drop_equation")
	| [  |- context[drop ?T ?thiss38 ?i] ] => 
			poseNew (Mark (T,thiss38,i) "unfolding drop_equation")
end.

Ltac rwrtTac_B106 := match goal with 
	| [ H1330: context[drop ?T ?thiss38 ?i], H2330: Marked (?T,?thiss38,?i) "unfolding drop_equation" |- _ ] => 
			poseNew (Mark (T,thiss38,i) "unfolded drop_equation");
			add_equation (drop_equation_1 T thiss38 i)
	| [ H2330: Marked (?T,?thiss38,?i) "unfolding drop_equation" |- context[drop ?T ?thiss38 ?i] ] => 
			poseNew (Mark (T,thiss38,i) "unfolded drop_equation");
			add_equation (drop_equation_1 T thiss38 i)
end.

Ltac rwrtTac106 := rwrtTac105; repeat rwrtTac_A106; repeat rwrtTac_B106.

Ltac t574 :=
  t_base ||
  List_tactic55 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t575 :=
  t574 ||
  rwrtTac106 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t575.

(***********************
  End of drop
 ***********************)


(***********************
  Start of replaceAtImpl
 ***********************)


Definition contractHyp164_type (T: Type) (thiss53: List T) (pos3: Z) (l3: List T) : Type :=
(ifthenelse (Z.leb (0)%Z pos3) bool
	(fun _ => Z.leb pos3 (proj1_sig (size T thiss53)) )
	(fun _ => false ) = true).

Fail Next Obligation.

Hint Unfold contractHyp164_type.


Definition replaceAtImpl_rt_type (T: Type) (thiss53: List T) (pos3: Z) (l3: List T) (contractHyp164: contractHyp164_type T thiss53 pos3 l3) : Type :=
{res18: List T | (set_subset (content T res18) (set_union (content T l3) (content T thiss53)) = true)}.

Fail Next Obligation.

Hint Unfold replaceAtImpl_rt_type.


Equations (noind) replaceAtImpl (T: Type) (thiss53: List T) (pos3: Z) (l3: List T) (contractHyp164: contractHyp164_type T thiss53 pos3 l3) : replaceAtImpl_rt_type T thiss53 pos3 l3 contractHyp164 := 
	replaceAtImpl T thiss53 pos3 l3 contractHyp164 by rec ignore_termination lt :=
	replaceAtImpl T thiss53 pos3 l3 contractHyp164 := ifthenelse (Zeq_bool pos3 (0)%Z) (List T)
		(fun _ => proj1_sig (plus_plus_ T l3 (proj1_sig (drop T thiss53 (proj1_sig (size T l3))))) )
		(fun _ => match thiss53 with
		| Cons_construct _ h23 t576 => 
				Cons_construct T h23 (proj1_sig (replaceAtImpl T t576 (Z.sub pos3 (1)%Z) l3 _))
		| Nil_construct _ => l3
		end ).

Hint Unfold replaceAtImpl_comp_proj.

Solve Obligations with (repeat t575).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A107 := match goal with 
	| [ H1331: context[replaceAtImpl ?T ?thiss53 ?pos3 ?l3] |- _ ] => 
			poseNew (Mark (T,thiss53,pos3,l3) "unfolding replaceAtImpl_equation")
	| [  |- context[replaceAtImpl ?T ?thiss53 ?pos3 ?l3] ] => 
			poseNew (Mark (T,thiss53,pos3,l3) "unfolding replaceAtImpl_equation")
end.

Ltac rwrtTac_B107 := match goal with 
	| [ H1331: context[replaceAtImpl ?T ?thiss53 ?pos3 ?l3], H2331: Marked (?T,?thiss53,?pos3,?l3) "unfolding replaceAtImpl_equation" |- _ ] => 
			poseNew (Mark (T,thiss53,pos3,l3) "unfolded replaceAtImpl_equation");
			add_equation (replaceAtImpl_equation_1 T thiss53 pos3 l3)
	| [ H2331: Marked (?T,?thiss53,?pos3,?l3) "unfolding replaceAtImpl_equation" |- context[replaceAtImpl ?T ?thiss53 ?pos3 ?l3] ] => 
			poseNew (Mark (T,thiss53,pos3,l3) "unfolded replaceAtImpl_equation");
			add_equation (replaceAtImpl_equation_1 T thiss53 pos3 l3)
end.

Ltac rwrtTac107 := rwrtTac106; repeat rwrtTac_A107; repeat rwrtTac_B107.

Ltac t577 :=
  t_base ||
  List_tactic55 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t578 :=
  t577 ||
  rwrtTac107 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t578.

(***********************
  End of replaceAtImpl
 ***********************)
