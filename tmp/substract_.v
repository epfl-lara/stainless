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

Ltac t289 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t290 :=
  t289 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t290.


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

Lemma None_exists: (forall T: Type, forall self280: Option T, ((true = isNone T self280)) <-> (((None_construct T = self280)))). 
Proof.
	repeat t290 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self281: Option T, ((true = isSome T self281)) <-> ((exists tmp105: T, (Some_construct T tmp105 = self281)))). 
Proof.
	repeat t290 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic35 := match goal with 
	| [ H140: (true = isNone ?T ?self282) |- _ ] => 
			poseNew (Mark (T,self282) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H140)
	| [ H140: (isNone ?T ?self282 = true) |- _ ] => 
			poseNew (Mark (T,self282) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H140))
	| [ H141: (true = isSome ?T ?self283) |- _ ] => 
			poseNew (Mark (T,self283) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H141)
	| [ H141: (isSome ?T ?self283 = true) |- _ ] => 
			poseNew (Mark (T,self283) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H141))
	| _ => idtac
end.

Ltac t291 :=
  t_base ||
  Option_tactic35 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t292 :=
  t291 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t292.


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

Lemma Cons_exists: (forall T: Type, forall self284: List T, ((true = isCons T self284)) <-> ((exists tmp107: List T, exists tmp106: T, (Cons_construct T tmp106 tmp107 = self284)))). 
Proof.
	repeat t292 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self285: List T, ((true = isNil T self285)) <-> (((Nil_construct T = self285)))). 
Proof.
	repeat t292 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic35 := match goal with 
	| [ H142: (true = isCons ?T ?self286) |- _ ] => 
			poseNew (Mark (T,self286) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H142)
	| [ H142: (isCons ?T ?self286 = true) |- _ ] => 
			poseNew (Mark (T,self286) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H142))
	| [ H143: (true = isNil ?T ?self287) |- _ ] => 
			poseNew (Mark (T,self287) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H143)
	| [ H143: (isNil ?T ?self287 = true) |- _ ] => 
			poseNew (Mark (T,self287) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H143))
	| _ => Option_tactic35
end.

Ltac t293 :=
  t_base ||
  List_tactic35 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t294 :=
  t293 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t294.

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
Definition content_rt8_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt8_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt8_type T thiss1 := 
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

Ltac rwrtTac_A31 := match goal with 
	| [ H1175: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B31 := match goal with 
	| [ H1175: context[content ?T ?thiss1], H2175: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2175: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac31 := idtac; repeat rwrtTac_A31; repeat rwrtTac_B31.

Ltac t295 :=
  t_base ||
  List_tactic35 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t296 :=
  t295 ||
  rwrtTac31 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t296.

(***********************
  End of content
 ***********************)

(***********************
  Start of contains
 ***********************)

Obligation Tactic:=idtac.
Definition contains_rt3_type (T: Type) (thiss2: List T) (v1: T) : Type :=
{x___2: bool | (Bool.eqb x___2 (set_elem_of v1 (content T thiss2)) = true)}.

Fail Next Obligation.

Hint Unfold contains_rt3_type.


Equations (noind) contains (T: Type) (thiss2: List T) (v1: T) : contains_rt3_type T thiss2 v1 := 
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

Ltac rwrtTac_A32 := match goal with 
	| [ H1176: context[contains ?T ?thiss2 ?v1] |- _ ] => 
			poseNew (Mark (T,thiss2,v1) "unfolding contains_equation")
	| [  |- context[contains ?T ?thiss2 ?v1] ] => 
			poseNew (Mark (T,thiss2,v1) "unfolding contains_equation")
end.

Ltac rwrtTac_B32 := match goal with 
	| [ H1176: context[contains ?T ?thiss2 ?v1], H2176: Marked (?T,?thiss2,?v1) "unfolding contains_equation" |- _ ] => 
			poseNew (Mark (T,thiss2,v1) "unfolded contains_equation");
			add_equation (contains_equation_1 T thiss2 v1)
	| [ H2176: Marked (?T,?thiss2,?v1) "unfolding contains_equation" |- context[contains ?T ?thiss2 ?v1] ] => 
			poseNew (Mark (T,thiss2,v1) "unfolded contains_equation");
			add_equation (contains_equation_1 T thiss2 v1)
end.

Ltac rwrtTac32 := rwrtTac31; repeat rwrtTac_A32; repeat rwrtTac_B32.

Ltac t297 :=
  t_base ||
  List_tactic35 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t298 :=
  t297 ||
  rwrtTac32 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t298.

(***********************
  End of contains
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt4_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt4_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt4_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A33 := match goal with 
	| [ H1177: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B33 := match goal with 
	| [ H1177: context[size ?T ?thiss30], H2177: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2177: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac33 := rwrtTac32; repeat rwrtTac_A33; repeat rwrtTac_B33.

Ltac t299 :=
  t_base ||
  List_tactic35 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t300 :=
  t299 ||
  rwrtTac33 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t300.

(***********************
  End of size
 ***********************)


(***********************
  Start of --
 ***********************)


Definition substract__rt_type (T: Type) (thiss34: List T) (that2: List T) : Type :=
{res5: List T | (ifthenelse (Z.leb (proj1_sig (size T res5)) (proj1_sig (size T thiss34))) bool
	(fun _ => set_equality (content T res5) (set_difference (content T thiss34) (content T that2)) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold substract__rt_type.


Equations (noind) substract_ (T: Type) (thiss34: List T) (that2: List T) : substract__rt_type T thiss34 that2 := 
	substract_ T thiss34 that2 by rec ignore_termination lt :=
	substract_ T thiss34 that2 := match thiss34 with
	| Cons_construct _ h15 t301 => 
			ifthenelse (proj1_sig (contains T that2 h15)) (List T)
				(fun _ => proj1_sig (substract_ T t301 that2) )
				(fun _ => Cons_construct T h15 (proj1_sig (substract_ T t301 that2)) )
	| Nil_construct _ => Nil_construct T
	end.

Hint Unfold substract__comp_proj.

Solve Obligations with (repeat t300).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A34 := match goal with 
	| [ H1178: context[substract_ ?T ?thiss34 ?that2] |- _ ] => 
			poseNew (Mark (T,thiss34,that2) "unfolding substract__equation")
	| [  |- context[substract_ ?T ?thiss34 ?that2] ] => 
			poseNew (Mark (T,thiss34,that2) "unfolding substract__equation")
end.

Ltac rwrtTac_B34 := match goal with 
	| [ H1178: context[substract_ ?T ?thiss34 ?that2], H2178: Marked (?T,?thiss34,?that2) "unfolding substract__equation" |- _ ] => 
			poseNew (Mark (T,thiss34,that2) "unfolded substract__equation");
			add_equation (substract__equation_1 T thiss34 that2)
	| [ H2178: Marked (?T,?thiss34,?that2) "unfolding substract__equation" |- context[substract_ ?T ?thiss34 ?that2] ] => 
			poseNew (Mark (T,thiss34,that2) "unfolded substract__equation");
			add_equation (substract__equation_1 T thiss34 that2)
end.

Ltac rwrtTac34 := rwrtTac33; repeat rwrtTac_A34; repeat rwrtTac_B34.

Ltac t302 :=
  t_base ||
  List_tactic35 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t303 :=
  t302 ||
  rwrtTac34 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t303.

(***********************
  End of --
 ***********************)
