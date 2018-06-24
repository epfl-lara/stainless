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

Ltac t264 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t265 :=
  t264 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t265.


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

Lemma None_exists: (forall T: Type, forall self264: Option T, ((true = isNone T self264)) <-> (((None_construct T = self264)))). 
Proof.
	repeat t265 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self265: Option T, ((true = isSome T self265)) <-> ((exists tmp99: T, (Some_construct T tmp99 = self265)))). 
Proof.
	repeat t265 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic33 := match goal with 
	| [ H132: (true = isNone ?T ?self266) |- _ ] => 
			poseNew (Mark (T,self266) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H132)
	| [ H132: (isNone ?T ?self266 = true) |- _ ] => 
			poseNew (Mark (T,self266) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H132))
	| [ H133: (true = isSome ?T ?self267) |- _ ] => 
			poseNew (Mark (T,self267) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H133)
	| [ H133: (isSome ?T ?self267 = true) |- _ ] => 
			poseNew (Mark (T,self267) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H133))
	| _ => idtac
end.

Ltac t266 :=
  t_base ||
  Option_tactic33 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t267 :=
  t266 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t267.


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

Lemma Cons_exists: (forall T: Type, forall self268: List T, ((true = isCons T self268)) <-> ((exists tmp101: List T, exists tmp100: T, (Cons_construct T tmp100 tmp101 = self268)))). 
Proof.
	repeat t267 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self269: List T, ((true = isNil T self269)) <-> (((Nil_construct T = self269)))). 
Proof.
	repeat t267 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic33 := match goal with 
	| [ H134: (true = isCons ?T ?self270) |- _ ] => 
			poseNew (Mark (T,self270) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H134)
	| [ H134: (isCons ?T ?self270 = true) |- _ ] => 
			poseNew (Mark (T,self270) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H134))
	| [ H135: (true = isNil ?T ?self271) |- _ ] => 
			poseNew (Mark (T,self271) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H135)
	| [ H135: (isNil ?T ?self271 = true) |- _ ] => 
			poseNew (Mark (T,self271) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H135))
	| _ => Option_tactic33
end.

Ltac t268 :=
  t_base ||
  List_tactic33 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t269 :=
  t268 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t269.

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
Definition content_rt6_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt6_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt6_type T thiss1 := 
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

Ltac rwrtTac_A25 := match goal with 
	| [ H1161: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B25 := match goal with 
	| [ H1161: context[content ?T ?thiss1], H2161: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2161: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac25 := idtac; repeat rwrtTac_A25; repeat rwrtTac_B25.

Ltac t270 :=
  t_base ||
  List_tactic33 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t271 :=
  t270 ||
  rwrtTac25 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t271.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt2_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt2_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt2_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A26 := match goal with 
	| [ H1162: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B26 := match goal with 
	| [ H1162: context[size ?T ?thiss30], H2162: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2162: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac26 := rwrtTac25; repeat rwrtTac_A26; repeat rwrtTac_B26.

Ltac t272 :=
  t_base ||
  List_tactic33 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t273 :=
  t272 ||
  rwrtTac26 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t273.

(***********************
  End of size
 ***********************)


(***********************
  Start of ++
 ***********************)


Definition plus_plus__rt_type (T: Type) (thiss32: List T) (that1: List T) : Type :=
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

Hint Unfold plus_plus__rt_type.


Equations (noind) plus_plus_ (T: Type) (thiss32: List T) (that1: List T) : plus_plus__rt_type T thiss32 that1 := 
	plus_plus_ T thiss32 that1 by rec ignore_termination lt :=
	plus_plus_ T thiss32 that1 := match thiss32 with
	| Nil_construct _ => that1
	| Cons_construct _ x2 xs => Cons_construct T x2 (proj1_sig (plus_plus_ T xs that1))
	end.

Hint Unfold plus_plus__comp_proj.

Solve Obligations with (repeat t273).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A27 := match goal with 
	| [ H1163: context[plus_plus_ ?T ?thiss32 ?that1] |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
	| [  |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
end.

Ltac rwrtTac_B27 := match goal with 
	| [ H1163: context[plus_plus_ ?T ?thiss32 ?that1], H2163: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
	| [ H2163: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
end.

Ltac rwrtTac27 := rwrtTac26; repeat rwrtTac_A27; repeat rwrtTac_B27.

Ltac t274 :=
  t_base ||
  List_tactic33 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t275 :=
  t274 ||
  rwrtTac27 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t275.

(***********************
  End of ++
 ***********************)
