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

Ltac t812 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t813 :=
  t812 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t813.


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

Lemma None_exists: (forall T: Type, forall self608: Option T, ((true = isNone T self608)) <-> (((None_construct T = self608)))). 
Proof.
	repeat t813 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self609: Option T, ((true = isSome T self609)) <-> ((exists tmp228: T, (Some_construct T tmp228 = self609)))). 
Proof.
	repeat t813 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic76 := match goal with 
	| [ H304: (true = isNone ?T ?self610) |- _ ] => 
			poseNew (Mark (T,self610) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H304)
	| [ H304: (isNone ?T ?self610 = true) |- _ ] => 
			poseNew (Mark (T,self610) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H304))
	| [ H305: (true = isSome ?T ?self611) |- _ ] => 
			poseNew (Mark (T,self611) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H305)
	| [ H305: (isSome ?T ?self611 = true) |- _ ] => 
			poseNew (Mark (T,self611) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H305))
	| _ => idtac
end.

Ltac t814 :=
  t_base ||
  Option_tactic76 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t815 :=
  t814 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t815.


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

Lemma Cons_exists: (forall T: Type, forall self612: List T, ((true = isCons T self612)) <-> ((exists tmp230: List T, exists tmp229: T, (Cons_construct T tmp229 tmp230 = self612)))). 
Proof.
	repeat t815 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self613: List T, ((true = isNil T self613)) <-> (((Nil_construct T = self613)))). 
Proof.
	repeat t815 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic76 := match goal with 
	| [ H306: (true = isCons ?T ?self614) |- _ ] => 
			poseNew (Mark (T,self614) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H306)
	| [ H306: (isCons ?T ?self614 = true) |- _ ] => 
			poseNew (Mark (T,self614) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H306))
	| [ H307: (true = isNil ?T ?self615) |- _ ] => 
			poseNew (Mark (T,self615) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H307)
	| [ H307: (isNil ?T ?self615 = true) |- _ ] => 
			poseNew (Mark (T,self615) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H307))
	| _ => Option_tactic76
end.

Ltac t816 :=
  t_base ||
  List_tactic76 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t817 :=
  t816 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t817.

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
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt37_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt37_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt37_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A163 := match goal with 
	| [ H1471: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B163 := match goal with 
	| [ H1471: context[size ?T ?thiss30], H2471: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2471: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac163 := idtac; repeat rwrtTac_A163; repeat rwrtTac_B163.

Ltac t818 :=
  t_base ||
  List_tactic76 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t819 :=
  t818 ||
  rwrtTac163 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t819.

(***********************
  End of size
 ***********************)


(***********************
  Start of zip
 ***********************)


Definition zip_rt_type (T: Type) (B: Type) (thiss73: List T) (that3: List B) : Type :=
{x___31: List ((T * B)%type) | (Zeq_bool (proj1_sig (size ((T * B)%type) x___31)) (ifthenelse (Z.leb (proj1_sig (size T thiss73)) (proj1_sig (size B that3))) Z
	(fun _ => proj1_sig (size T thiss73) )
	(fun _ => proj1_sig (size B that3) )) = true)}.

Fail Next Obligation.

Hint Unfold zip_rt_type.


Equations (noind) zip (T: Type) (B: Type) (thiss73: List T) (that3: List B) : zip_rt_type T B thiss73 that3 := 
	zip T B thiss73 that3 by rec ignore_termination lt :=
	zip T B thiss73 that3 := ifthenelse
		(ifthenelse (isCons _ thiss73) bool
			(fun _ => isCons _ that3 )
			(fun _ => false ))
		(List ((T * B)%type))
		(fun _ => Cons_construct ((T * B)%type) ((h T thiss73,h B that3)) (proj1_sig (zip T B (t7 T thiss73) (t7 B that3))) )
		(fun _ => Nil_construct ((T * B)%type) ).

Hint Unfold zip_comp_proj.

Solve Obligations with (repeat t819).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A164 := match goal with 
	| [ H1472: context[zip ?T ?B ?thiss73 ?that3] |- _ ] => 
			poseNew (Mark (T,B,thiss73,that3) "unfolding zip_equation")
	| [  |- context[zip ?T ?B ?thiss73 ?that3] ] => 
			poseNew (Mark (T,B,thiss73,that3) "unfolding zip_equation")
end.

Ltac rwrtTac_B164 := match goal with 
	| [ H1472: context[zip ?T ?B ?thiss73 ?that3], H2472: Marked (?T,?B,?thiss73,?that3) "unfolding zip_equation" |- _ ] => 
			poseNew (Mark (T,B,thiss73,that3) "unfolded zip_equation");
			add_equation (zip_equation_1 T B thiss73 that3)
	| [ H2472: Marked (?T,?B,?thiss73,?that3) "unfolding zip_equation" |- context[zip ?T ?B ?thiss73 ?that3] ] => 
			poseNew (Mark (T,B,thiss73,that3) "unfolded zip_equation");
			add_equation (zip_equation_1 T B thiss73 that3)
end.

Ltac rwrtTac164 := rwrtTac163; repeat rwrtTac_A164; repeat rwrtTac_B164.

Ltac t820 :=
  t_base ||
  List_tactic76 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t821 :=
  t820 ||
  rwrtTac164 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t821.

(***********************
  End of zip
 ***********************)
