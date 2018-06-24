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

Ltac t249 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t250 :=
  t249 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t250.


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

Lemma None_exists: (forall T: Type, forall self256: Option T, ((true = isNone T self256)) <-> (((None_construct T = self256)))). 
Proof.
	repeat t250 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self257: Option T, ((true = isSome T self257)) <-> ((exists tmp96: T, (Some_construct T tmp96 = self257)))). 
Proof.
	repeat t250 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic32 := match goal with 
	| [ H128: (true = isNone ?T ?self258) |- _ ] => 
			poseNew (Mark (T,self258) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H128)
	| [ H128: (isNone ?T ?self258 = true) |- _ ] => 
			poseNew (Mark (T,self258) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H128))
	| [ H129: (true = isSome ?T ?self259) |- _ ] => 
			poseNew (Mark (T,self259) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H129)
	| [ H129: (isSome ?T ?self259 = true) |- _ ] => 
			poseNew (Mark (T,self259) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H129))
	| _ => idtac
end.

Ltac t251 :=
  t_base ||
  Option_tactic32 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t252 :=
  t251 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t252.


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

Lemma Cons_exists: (forall T: Type, forall self260: List T, ((true = isCons T self260)) <-> ((exists tmp98: List T, exists tmp97: T, (Cons_construct T tmp97 tmp98 = self260)))). 
Proof.
	repeat t252 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self261: List T, ((true = isNil T self261)) <-> (((Nil_construct T = self261)))). 
Proof.
	repeat t252 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic32 := match goal with 
	| [ H130: (true = isCons ?T ?self262) |- _ ] => 
			poseNew (Mark (T,self262) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H130)
	| [ H130: (isCons ?T ?self262 = true) |- _ ] => 
			poseNew (Mark (T,self262) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H130))
	| [ H131: (true = isNil ?T ?self263) |- _ ] => 
			poseNew (Mark (T,self263) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H131)
	| [ H131: (isNil ?T ?self263 = true) |- _ ] => 
			poseNew (Mark (T,self263) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H131))
	| _ => Option_tactic32
end.

Ltac t253 :=
  t_base ||
  List_tactic32 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t254 :=
  t253 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t254.

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
Definition content_rt5_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt5_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt5_type T thiss1 := 
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

Ltac rwrtTac_A21 := match goal with 
	| [ H1153: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B21 := match goal with 
	| [ H1153: context[content ?T ?thiss1], H2153: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2153: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac21 := idtac; repeat rwrtTac_A21; repeat rwrtTac_B21.

Ltac t255 :=
  t_base ||
  List_tactic32 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t256 :=
  t255 ||
  rwrtTac21 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t256.

(***********************
  End of content
 ***********************)

(***********************
  Start of contains
 ***********************)

Obligation Tactic:=idtac.
Definition contains_rt2_type (T: Type) (thiss2: List T) (v1: T) : Type :=
{x___2: bool | (Bool.eqb x___2 (set_elem_of v1 (content T thiss2)) = true)}.

Fail Next Obligation.

Hint Unfold contains_rt2_type.


Equations (noind) contains (T: Type) (thiss2: List T) (v1: T) : contains_rt2_type T thiss2 v1 := 
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

Ltac rwrtTac_A22 := match goal with 
	| [ H1154: context[contains ?T ?thiss2 ?v1] |- _ ] => 
			poseNew (Mark (T,thiss2,v1) "unfolding contains_equation")
	| [  |- context[contains ?T ?thiss2 ?v1] ] => 
			poseNew (Mark (T,thiss2,v1) "unfolding contains_equation")
end.

Ltac rwrtTac_B22 := match goal with 
	| [ H1154: context[contains ?T ?thiss2 ?v1], H2154: Marked (?T,?thiss2,?v1) "unfolding contains_equation" |- _ ] => 
			poseNew (Mark (T,thiss2,v1) "unfolded contains_equation");
			add_equation (contains_equation_1 T thiss2 v1)
	| [ H2154: Marked (?T,?thiss2,?v1) "unfolding contains_equation" |- context[contains ?T ?thiss2 ?v1] ] => 
			poseNew (Mark (T,thiss2,v1) "unfolded contains_equation");
			add_equation (contains_equation_1 T thiss2 v1)
end.

Ltac rwrtTac22 := rwrtTac21; repeat rwrtTac_A22; repeat rwrtTac_B22.

Ltac t257 :=
  t_base ||
  List_tactic32 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t258 :=
  t257 ||
  rwrtTac22 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t258.

(***********************
  End of contains
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt1_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt1_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt1_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A23 := match goal with 
	| [ H1155: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B23 := match goal with 
	| [ H1155: context[size ?T ?thiss30], H2155: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2155: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac23 := rwrtTac22; repeat rwrtTac_A23; repeat rwrtTac_B23.

Ltac t259 :=
  t_base ||
  List_tactic32 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t260 :=
  t259 ||
  rwrtTac23 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t260.

(***********************
  End of size
 ***********************)


(***********************
  Start of &
 ***********************)


Definition c__rt_type (T: Type) (thiss31: List T) (that: List T) : Type :=
{res2: List T | (ifthenelse (Z.leb (proj1_sig (size T res2)) (proj1_sig (size T thiss31))) bool
	(fun _ => set_equality (content T res2) (set_intersection (content T thiss31) (content T that)) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold c__rt_type.


Equations (noind) c_ (T: Type) (thiss31: List T) (that: List T) : c__rt_type T thiss31 that := 
	c_ T thiss31 that by rec ignore_termination lt :=
	c_ T thiss31 that := match thiss31 with
	| Cons_construct _ h13 t261 => 
			ifthenelse (proj1_sig (contains T that h13)) (List T)
				(fun _ => Cons_construct T h13 (proj1_sig (c_ T t261 that)) )
				(fun _ => proj1_sig (c_ T t261 that) )
	| Nil_construct _ => Nil_construct T
	end.

Hint Unfold c__comp_proj.

Solve Obligations with (repeat t260).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A24 := match goal with 
	| [ H1156: context[c_ ?T ?thiss31 ?that] |- _ ] => 
			poseNew (Mark (T,thiss31,that) "unfolding c__equation")
	| [  |- context[c_ ?T ?thiss31 ?that] ] => 
			poseNew (Mark (T,thiss31,that) "unfolding c__equation")
end.

Ltac rwrtTac_B24 := match goal with 
	| [ H1156: context[c_ ?T ?thiss31 ?that], H2156: Marked (?T,?thiss31,?that) "unfolding c__equation" |- _ ] => 
			poseNew (Mark (T,thiss31,that) "unfolded c__equation");
			add_equation (c__equation_1 T thiss31 that)
	| [ H2156: Marked (?T,?thiss31,?that) "unfolding c__equation" |- context[c_ ?T ?thiss31 ?that] ] => 
			poseNew (Mark (T,thiss31,that) "unfolded c__equation");
			add_equation (c__equation_1 T thiss31 that)
end.

Ltac rwrtTac24 := rwrtTac23; repeat rwrtTac_A24; repeat rwrtTac_B24.

Ltac t262 :=
  t_base ||
  List_tactic32 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t263 :=
  t262 ||
  rwrtTac24 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t263.

(***********************
  End of &
 ***********************)
