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

Ltac t358 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t359 :=
  t358 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t359.


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

Lemma None_exists: (forall T: Type, forall self320: Option T, ((true = isNone T self320)) <-> (((None_construct T = self320)))). 
Proof.
	repeat t359 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self321: Option T, ((true = isSome T self321)) <-> ((exists tmp120: T, (Some_construct T tmp120 = self321)))). 
Proof.
	repeat t359 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic40 := match goal with 
	| [ H160: (true = isNone ?T ?self322) |- _ ] => 
			poseNew (Mark (T,self322) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H160)
	| [ H160: (isNone ?T ?self322 = true) |- _ ] => 
			poseNew (Mark (T,self322) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H160))
	| [ H161: (true = isSome ?T ?self323) |- _ ] => 
			poseNew (Mark (T,self323) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H161)
	| [ H161: (isSome ?T ?self323 = true) |- _ ] => 
			poseNew (Mark (T,self323) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H161))
	| _ => idtac
end.

Ltac t360 :=
  t_base ||
  Option_tactic40 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t361 :=
  t360 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t361.


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

Lemma Cons_exists: (forall T: Type, forall self324: List T, ((true = isCons T self324)) <-> ((exists tmp122: List T, exists tmp121: T, (Cons_construct T tmp121 tmp122 = self324)))). 
Proof.
	repeat t361 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self325: List T, ((true = isNil T self325)) <-> (((Nil_construct T = self325)))). 
Proof.
	repeat t361 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic40 := match goal with 
	| [ H162: (true = isCons ?T ?self326) |- _ ] => 
			poseNew (Mark (T,self326) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H162)
	| [ H162: (isCons ?T ?self326 = true) |- _ ] => 
			poseNew (Mark (T,self326) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H162))
	| [ H163: (true = isNil ?T ?self327) |- _ ] => 
			poseNew (Mark (T,self327) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H163)
	| [ H163: (isNil ?T ?self327 = true) |- _ ] => 
			poseNew (Mark (T,self327) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H163))
	| _ => Option_tactic40
end.

Ltac t362 :=
  t_base ||
  List_tactic40 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t363 :=
  t362 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t363.

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
Definition content_rt13_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt13_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt13_type T thiss1 := 
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

Ltac rwrtTac_A49 := match goal with 
	| [ H1213: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B49 := match goal with 
	| [ H1213: context[content ?T ?thiss1], H2213: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2213: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac49 := idtac; repeat rwrtTac_A49; repeat rwrtTac_B49.

Ltac t364 :=
  t_base ||
  List_tactic40 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t365 :=
  t364 ||
  rwrtTac49 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t365.

(***********************
  End of content
 ***********************)

(***********************
  Start of head
 ***********************)

Definition head (T: Type) (thiss14: List T) (contractHyp94: (negb (propInBool ((thiss14 = Nil_construct T))) = true)) : T :=
ifthenelse (isCons _ thiss14) T
	(fun _ => h T thiss14 )
	(fun _ => let contradiction: False := _ in match contradiction with end ).

Fail Next Obligation.

Hint Unfold head: definitions.

(***********************
  End of head
 ***********************)

(***********************
  Start of isEmpty
 ***********************)

Definition isEmpty (T: Type) (thiss17: List T) : bool :=
ifthenelse (isNil _ thiss17) bool
	(fun _ => true )
	(fun _ => false ).

Fail Next Obligation.

Hint Unfold isEmpty: definitions.

(***********************
  End of isEmpty
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt9_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt9_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt9_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A50 := match goal with 
	| [ H1214: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B50 := match goal with 
	| [ H1214: context[size ?T ?thiss30], H2214: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2214: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac50 := rwrtTac49; repeat rwrtTac_A50; repeat rwrtTac_B50.

Ltac t366 :=
  t_base ||
  List_tactic40 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t367 :=
  t366 ||
  rwrtTac50 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t367.

(***********************
  End of size
 ***********************)


(***********************
  Start of dropWhile
 ***********************)


Definition dropWhile_rt_type (T: Type) (thiss39: List T) (p7: T -> bool) : Type :=
{res9: List T | (ifthenelse
	(ifthenelse (Z.leb (proj1_sig (size T res9)) (proj1_sig (size T thiss39))) bool
		(fun _ => set_subset (content T res9) (content T thiss39) )
		(fun _ => false ))
	bool
	(fun _ => ifthenelse (isEmpty T res9) bool
		(fun _ => true )
		(fun _ => negb (p7 (head T res9 _)) ) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold dropWhile_rt_type.


Equations (noind) dropWhile (T: Type) (thiss39: List T) (p7: T -> bool) : dropWhile_rt_type T thiss39 p7 := 
	dropWhile T thiss39 p7 by rec ignore_termination lt :=
	dropWhile T thiss39 p7 := ifthenelse
		(ifthenelse (isCons _ thiss39) bool
			(fun _ => p7 (h T thiss39) )
			(fun _ => false ))
		(List T)
		(fun _ => proj1_sig (dropWhile T (t7 T thiss39) p7) )
		(fun _ => thiss39 ).

Hint Unfold dropWhile_comp_proj.

Solve Obligations with (repeat t367).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A51 := match goal with 
	| [ H1215: context[dropWhile ?T ?thiss39 ?p7] |- _ ] => 
			poseNew (Mark (T,thiss39,p7) "unfolding dropWhile_equation")
	| [  |- context[dropWhile ?T ?thiss39 ?p7] ] => 
			poseNew (Mark (T,thiss39,p7) "unfolding dropWhile_equation")
end.

Ltac rwrtTac_B51 := match goal with 
	| [ H1215: context[dropWhile ?T ?thiss39 ?p7], H2215: Marked (?T,?thiss39,?p7) "unfolding dropWhile_equation" |- _ ] => 
			poseNew (Mark (T,thiss39,p7) "unfolded dropWhile_equation");
			add_equation (dropWhile_equation_1 T thiss39 p7)
	| [ H2215: Marked (?T,?thiss39,?p7) "unfolding dropWhile_equation" |- context[dropWhile ?T ?thiss39 ?p7] ] => 
			poseNew (Mark (T,thiss39,p7) "unfolded dropWhile_equation");
			add_equation (dropWhile_equation_1 T thiss39 p7)
end.

Ltac rwrtTac51 := rwrtTac50; repeat rwrtTac_A51; repeat rwrtTac_B51.

Ltac t368 :=
  t_base ||
  List_tactic40 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t369 :=
  t368 ||
  rwrtTac51 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t369.

(***********************
  End of dropWhile
 ***********************)
