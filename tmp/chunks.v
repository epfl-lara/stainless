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

Ltac t332 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t333 :=
  t332 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t333.


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

Lemma None_exists: (forall T: Type, forall self304: Option T, ((true = isNone T self304)) <-> (((None_construct T = self304)))). 
Proof.
	repeat t333 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self305: Option T, ((true = isSome T self305)) <-> ((exists tmp114: T, (Some_construct T tmp114 = self305)))). 
Proof.
	repeat t333 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic38 := match goal with 
	| [ H152: (true = isNone ?T ?self306) |- _ ] => 
			poseNew (Mark (T,self306) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H152)
	| [ H152: (isNone ?T ?self306 = true) |- _ ] => 
			poseNew (Mark (T,self306) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H152))
	| [ H153: (true = isSome ?T ?self307) |- _ ] => 
			poseNew (Mark (T,self307) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H153)
	| [ H153: (isSome ?T ?self307 = true) |- _ ] => 
			poseNew (Mark (T,self307) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H153))
	| _ => idtac
end.

Ltac t334 :=
  t_base ||
  Option_tactic38 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t335 :=
  t334 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t335.


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

Lemma Cons_exists: (forall T: Type, forall self308: List T, ((true = isCons T self308)) <-> ((exists tmp116: List T, exists tmp115: T, (Cons_construct T tmp115 tmp116 = self308)))). 
Proof.
	repeat t335 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self309: List T, ((true = isNil T self309)) <-> (((Nil_construct T = self309)))). 
Proof.
	repeat t335 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic38 := match goal with 
	| [ H154: (true = isCons ?T ?self310) |- _ ] => 
			poseNew (Mark (T,self310) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H154)
	| [ H154: (isCons ?T ?self310 = true) |- _ ] => 
			poseNew (Mark (T,self310) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H154))
	| [ H155: (true = isNil ?T ?self311) |- _ ] => 
			poseNew (Mark (T,self311) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H155)
	| [ H155: (isNil ?T ?self311 = true) |- _ ] => 
			poseNew (Mark (T,self311) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H155))
	| _ => Option_tactic38
end.

Ltac t336 :=
  t_base ||
  List_tactic38 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t337 :=
  t336 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t337.

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
Definition content_rt11_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt11_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt11_type T thiss1 := 
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

Ltac rwrtTac_A42 := match goal with 
	| [ H1198: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B42 := match goal with 
	| [ H1198: context[content ?T ?thiss1], H2198: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2198: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac42 := idtac; repeat rwrtTac_A42; repeat rwrtTac_B42.

Ltac t338 :=
  t_base ||
  List_tactic38 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t339 :=
  t338 ||
  rwrtTac42 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t339.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt7_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt7_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt7_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A43 := match goal with 
	| [ H1199: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B43 := match goal with 
	| [ H1199: context[size ?T ?thiss30], H2199: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2199: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac43 := rwrtTac42; repeat rwrtTac_A43; repeat rwrtTac_B43.

Ltac t340 :=
  t_base ||
  List_tactic38 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t341 :=
  t340 ||
  rwrtTac43 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t341.

(***********************
  End of size
 ***********************)

(***********************
  Start of :+
 ***********************)

Obligation Tactic:=idtac.
Definition snoc__rt2_type (T: Type) (thiss35: List T) (t314: T) : Type :=
{res6: List T | (let assumption2 := (magic ((isCons _ res6 = true))) in (ifthenelse (Zeq_bool (proj1_sig (size T res6)) (Z.add (proj1_sig (size T thiss35)) (1)%Z)) bool
	(fun _ => set_equality (content T res6) (set_union (content T thiss35) (set_union (@set_empty T) (set_singleton t314))) )
	(fun _ => false )) = true)}.

Fail Next Obligation.

Hint Unfold snoc__rt2_type.


Equations (noind) snoc_ (T: Type) (thiss35: List T) (t314: T) : snoc__rt2_type T thiss35 t314 := 
	snoc_ T thiss35 t314 by rec ignore_termination lt :=
	snoc_ T thiss35 t314 := match thiss35 with
	| Nil_construct _ => Cons_construct T t314 thiss35
	| Cons_construct _ x3 xs1 => Cons_construct T x3 (proj1_sig (snoc_ T xs1 t314))
	end.

Hint Unfold snoc__comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A44 := match goal with 
	| [ H1200: context[snoc_ ?T ?thiss35 ?t314] |- _ ] => 
			poseNew (Mark (T,thiss35,t314) "unfolding snoc__equation")
	| [  |- context[snoc_ ?T ?thiss35 ?t314] ] => 
			poseNew (Mark (T,thiss35,t314) "unfolding snoc__equation")
end.

Ltac rwrtTac_B44 := match goal with 
	| [ H1200: context[snoc_ ?T ?thiss35 ?t314], H2200: Marked (?T,?thiss35,?t314) "unfolding snoc__equation" |- _ ] => 
			poseNew (Mark (T,thiss35,t314) "unfolded snoc__equation");
			add_equation (snoc__equation_1 T thiss35 t314)
	| [ H2200: Marked (?T,?thiss35,?t314) "unfolding snoc__equation" |- context[snoc_ ?T ?thiss35 ?t314] ] => 
			poseNew (Mark (T,thiss35,t314) "unfolded snoc__equation");
			add_equation (snoc__equation_1 T thiss35 t314)
end.

Ltac rwrtTac44 := rwrtTac43; repeat rwrtTac_A44; repeat rwrtTac_B44.

Ltac t342 :=
  t_base ||
  List_tactic38 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t343 :=
  t342 ||
  rwrtTac44 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t343.

(***********************
  End of :+
 ***********************)

(***********************
  Start of chunk0
 ***********************)

Obligation Tactic:=idtac.
Definition contractHyp88_type (T: Type) (thiss36: List T) (s: Z) (l: List T) (acc: List T) (res7: List (List T)) (s0: Z) : Type :=
(ifthenelse (Z.gtb s (0)%Z) bool
	(fun _ => Z.geb s0 (0)%Z )
	(fun _ => false ) = true).

Fail Next Obligation.

Hint Unfold contractHyp88_type.


Definition chunk0_rt1_type (T: Type) (thiss36: List T) (s: Z) (l: List T) (acc: List T) (res7: List (List T)) (s0: Z) (contractHyp88: contractHyp88_type T thiss36 s l acc res7 s0) : Type :=
List (List T).

Fail Next Obligation.

Hint Unfold chunk0_rt1_type.


Equations (noind) chunk0 (T: Type) (thiss36: List T) (s: Z) (l: List T) (acc: List T) (res7: List (List T)) (s0: Z) (contractHyp88: contractHyp88_type T thiss36 s l acc res7 s0) : chunk0_rt1_type T thiss36 s l acc res7 s0 contractHyp88 := 
	chunk0 T thiss36 s l acc res7 s0 contractHyp88 by rec ignore_termination lt :=
	chunk0 T thiss36 s l acc res7 s0 contractHyp88 := match l with
	| Nil_construct _ => 
			ifthenelse (Z.gtb (proj1_sig (size T acc)) (0)%Z) (List (List T))
				(fun _ => proj1_sig (snoc_ (List T) res7 acc) )
				(fun _ => res7 )
	| Cons_construct _ h16 t329 => 
			ifthenelse (Zeq_bool s0 (0)%Z) (List (List T))
				(fun _ => chunk0 T thiss36 s t329 (Cons_construct T h16 (Nil_construct T)) (proj1_sig (snoc_ (List T) res7 acc)) (Z.sub s (1)%Z) _ )
				(fun _ => chunk0 T thiss36 s t329 (proj1_sig (snoc_ T acc h16)) res7 (Z.sub s0 (1)%Z) _ )
	end.

Hint Unfold chunk0_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A45 := match goal with 
	| [ H1201: context[chunk0 ?T ?thiss36 ?s ?l ?acc ?res7 ?s0] |- _ ] => 
			poseNew (Mark (T,thiss36,s,l,acc,res7,s0) "unfolding chunk0_equation")
	| [  |- context[chunk0 ?T ?thiss36 ?s ?l ?acc ?res7 ?s0] ] => 
			poseNew (Mark (T,thiss36,s,l,acc,res7,s0) "unfolding chunk0_equation")
end.

Ltac rwrtTac_B45 := match goal with 
	| [ H1201: context[chunk0 ?T ?thiss36 ?s ?l ?acc ?res7 ?s0], H2201: Marked (?T,?thiss36,?s,?l,?acc,?res7,?s0) "unfolding chunk0_equation" |- _ ] => 
			poseNew (Mark (T,thiss36,s,l,acc,res7,s0) "unfolded chunk0_equation");
			add_equation (chunk0_equation_1 T thiss36 s l acc res7 s0)
	| [ H2201: Marked (?T,?thiss36,?s,?l,?acc,?res7,?s0) "unfolding chunk0_equation" |- context[chunk0 ?T ?thiss36 ?s ?l ?acc ?res7 ?s0] ] => 
			poseNew (Mark (T,thiss36,s,l,acc,res7,s0) "unfolded chunk0_equation");
			add_equation (chunk0_equation_1 T thiss36 s l acc res7 s0)
end.

Ltac rwrtTac45 := rwrtTac44; repeat rwrtTac_A45; repeat rwrtTac_B45.

Ltac t344 :=
  t_base ||
  List_tactic38 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t345 :=
  t344 ||
  rwrtTac45 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t345.

(***********************
  End of chunk0
 ***********************)


(***********************
  Start of chunks
 ***********************)

Definition chunks (T: Type) (thiss37: List T) (s1: Z) (contractHyp89: (Z.gtb s1 (0)%Z = true)) : List (List T) :=
chunk0 T thiss37 s1 thiss37 (Nil_construct T) (Nil_construct (List T)) s1 _.

Fail Next Obligation.

Hint Unfold chunks: definitions.

(***********************
  End of chunks
 ***********************)
