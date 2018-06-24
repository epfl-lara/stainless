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

Ltac t317 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t318 :=
  t317 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t318.


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

Lemma None_exists: (forall T: Type, forall self296: Option T, ((true = isNone T self296)) <-> (((None_construct T = self296)))). 
Proof.
	repeat t318 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self297: Option T, ((true = isSome T self297)) <-> ((exists tmp111: T, (Some_construct T tmp111 = self297)))). 
Proof.
	repeat t318 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic37 := match goal with 
	| [ H148: (true = isNone ?T ?self298) |- _ ] => 
			poseNew (Mark (T,self298) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H148)
	| [ H148: (isNone ?T ?self298 = true) |- _ ] => 
			poseNew (Mark (T,self298) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H148))
	| [ H149: (true = isSome ?T ?self299) |- _ ] => 
			poseNew (Mark (T,self299) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H149)
	| [ H149: (isSome ?T ?self299 = true) |- _ ] => 
			poseNew (Mark (T,self299) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H149))
	| _ => idtac
end.

Ltac t319 :=
  t_base ||
  Option_tactic37 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t320 :=
  t319 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t320.


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

Lemma Cons_exists: (forall T: Type, forall self300: List T, ((true = isCons T self300)) <-> ((exists tmp113: List T, exists tmp112: T, (Cons_construct T tmp112 tmp113 = self300)))). 
Proof.
	repeat t320 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self301: List T, ((true = isNil T self301)) <-> (((Nil_construct T = self301)))). 
Proof.
	repeat t320 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic37 := match goal with 
	| [ H150: (true = isCons ?T ?self302) |- _ ] => 
			poseNew (Mark (T,self302) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H150)
	| [ H150: (isCons ?T ?self302 = true) |- _ ] => 
			poseNew (Mark (T,self302) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H150))
	| [ H151: (true = isNil ?T ?self303) |- _ ] => 
			poseNew (Mark (T,self303) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H151)
	| [ H151: (isNil ?T ?self303 = true) |- _ ] => 
			poseNew (Mark (T,self303) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H151))
	| _ => Option_tactic37
end.

Ltac t321 :=
  t_base ||
  List_tactic37 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t322 :=
  t321 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t322.

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
Definition content_rt10_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt10_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt10_type T thiss1 := 
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

Ltac rwrtTac_A38 := match goal with 
	| [ H1190: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B38 := match goal with 
	| [ H1190: context[content ?T ?thiss1], H2190: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2190: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac38 := idtac; repeat rwrtTac_A38; repeat rwrtTac_B38.

Ltac t323 :=
  t_base ||
  List_tactic37 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t324 :=
  t323 ||
  rwrtTac38 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t324.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt6_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt6_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt6_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A39 := match goal with 
	| [ H1191: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B39 := match goal with 
	| [ H1191: context[size ?T ?thiss30], H2191: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2191: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac39 := rwrtTac38; repeat rwrtTac_A39; repeat rwrtTac_B39.

Ltac t325 :=
  t_base ||
  List_tactic37 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t326 :=
  t325 ||
  rwrtTac39 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t326.

(***********************
  End of size
 ***********************)

(***********************
  Start of :+
 ***********************)

Obligation Tactic:=idtac.
Definition snoc__rt1_type (T: Type) (thiss35: List T) (t314: T) : Type :=
{res6: List T | (let assumption1 := (magic ((isCons _ res6 = true))) in (ifthenelse (Zeq_bool (proj1_sig (size T res6)) (Z.add (proj1_sig (size T thiss35)) (1)%Z)) bool
	(fun _ => set_equality (content T res6) (set_union (content T thiss35) (set_union (@set_empty T) (set_singleton t314))) )
	(fun _ => false )) = true)}.

Fail Next Obligation.

Hint Unfold snoc__rt1_type.


Equations (noind) snoc_ (T: Type) (thiss35: List T) (t314: T) : snoc__rt1_type T thiss35 t314 := 
	snoc_ T thiss35 t314 by rec ignore_termination lt :=
	snoc_ T thiss35 t314 := match thiss35 with
	| Nil_construct _ => Cons_construct T t314 thiss35
	| Cons_construct _ x3 xs1 => Cons_construct T x3 (proj1_sig (snoc_ T xs1 t314))
	end.

Hint Unfold snoc__comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A40 := match goal with 
	| [ H1192: context[snoc_ ?T ?thiss35 ?t314] |- _ ] => 
			poseNew (Mark (T,thiss35,t314) "unfolding snoc__equation")
	| [  |- context[snoc_ ?T ?thiss35 ?t314] ] => 
			poseNew (Mark (T,thiss35,t314) "unfolding snoc__equation")
end.

Ltac rwrtTac_B40 := match goal with 
	| [ H1192: context[snoc_ ?T ?thiss35 ?t314], H2192: Marked (?T,?thiss35,?t314) "unfolding snoc__equation" |- _ ] => 
			poseNew (Mark (T,thiss35,t314) "unfolded snoc__equation");
			add_equation (snoc__equation_1 T thiss35 t314)
	| [ H2192: Marked (?T,?thiss35,?t314) "unfolding snoc__equation" |- context[snoc_ ?T ?thiss35 ?t314] ] => 
			poseNew (Mark (T,thiss35,t314) "unfolded snoc__equation");
			add_equation (snoc__equation_1 T thiss35 t314)
end.

Ltac rwrtTac40 := rwrtTac39; repeat rwrtTac_A40; repeat rwrtTac_B40.

Ltac t327 :=
  t_base ||
  List_tactic37 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t328 :=
  t327 ||
  rwrtTac40 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t328.

(***********************
  End of :+
 ***********************)


(***********************
  Start of chunk0
 ***********************)


Definition contractHyp84_type (T: Type) (thiss36: List T) (s: Z) (l: List T) (acc: List T) (res7: List (List T)) (s0: Z) : Type :=
(ifthenelse (Z.gtb s (0)%Z) bool
	(fun _ => Z.geb s0 (0)%Z )
	(fun _ => false ) = true).

Fail Next Obligation.

Hint Unfold contractHyp84_type.


Definition chunk0_rt_type (T: Type) (thiss36: List T) (s: Z) (l: List T) (acc: List T) (res7: List (List T)) (s0: Z) (contractHyp84: contractHyp84_type T thiss36 s l acc res7 s0) : Type :=
List (List T).

Fail Next Obligation.

Hint Unfold chunk0_rt_type.


Equations (noind) chunk0 (T: Type) (thiss36: List T) (s: Z) (l: List T) (acc: List T) (res7: List (List T)) (s0: Z) (contractHyp84: contractHyp84_type T thiss36 s l acc res7 s0) : chunk0_rt_type T thiss36 s l acc res7 s0 contractHyp84 := 
	chunk0 T thiss36 s l acc res7 s0 contractHyp84 by rec ignore_termination lt :=
	chunk0 T thiss36 s l acc res7 s0 contractHyp84 := match l with
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

Solve Obligations with (repeat t328).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A41 := match goal with 
	| [ H1193: context[chunk0 ?T ?thiss36 ?s ?l ?acc ?res7 ?s0] |- _ ] => 
			poseNew (Mark (T,thiss36,s,l,acc,res7,s0) "unfolding chunk0_equation")
	| [  |- context[chunk0 ?T ?thiss36 ?s ?l ?acc ?res7 ?s0] ] => 
			poseNew (Mark (T,thiss36,s,l,acc,res7,s0) "unfolding chunk0_equation")
end.

Ltac rwrtTac_B41 := match goal with 
	| [ H1193: context[chunk0 ?T ?thiss36 ?s ?l ?acc ?res7 ?s0], H2193: Marked (?T,?thiss36,?s,?l,?acc,?res7,?s0) "unfolding chunk0_equation" |- _ ] => 
			poseNew (Mark (T,thiss36,s,l,acc,res7,s0) "unfolded chunk0_equation");
			add_equation (chunk0_equation_1 T thiss36 s l acc res7 s0)
	| [ H2193: Marked (?T,?thiss36,?s,?l,?acc,?res7,?s0) "unfolding chunk0_equation" |- context[chunk0 ?T ?thiss36 ?s ?l ?acc ?res7 ?s0] ] => 
			poseNew (Mark (T,thiss36,s,l,acc,res7,s0) "unfolded chunk0_equation");
			add_equation (chunk0_equation_1 T thiss36 s l acc res7 s0)
end.

Ltac rwrtTac41 := rwrtTac40; repeat rwrtTac_A41; repeat rwrtTac_B41.

Ltac t330 :=
  t_base ||
  List_tactic37 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t331 :=
  t330 ||
  rwrtTac41 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t331.

(***********************
  End of chunk0
 ***********************)
