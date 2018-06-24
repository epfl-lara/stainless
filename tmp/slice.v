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

Ltac t707 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t708 :=
  t707 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t708.


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

Lemma None_exists: (forall T: Type, forall self536: Option T, ((true = isNone T self536)) <-> (((None_construct T = self536)))). 
Proof.
	repeat t708 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self537: Option T, ((true = isSome T self537)) <-> ((exists tmp201: T, (Some_construct T tmp201 = self537)))). 
Proof.
	repeat t708 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic67 := match goal with 
	| [ H268: (true = isNone ?T ?self538) |- _ ] => 
			poseNew (Mark (T,self538) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H268)
	| [ H268: (isNone ?T ?self538 = true) |- _ ] => 
			poseNew (Mark (T,self538) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H268))
	| [ H269: (true = isSome ?T ?self539) |- _ ] => 
			poseNew (Mark (T,self539) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H269)
	| [ H269: (isSome ?T ?self539 = true) |- _ ] => 
			poseNew (Mark (T,self539) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H269))
	| _ => idtac
end.

Ltac t709 :=
  t_base ||
  Option_tactic67 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t710 :=
  t709 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t710.


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

Lemma Cons_exists: (forall T: Type, forall self540: List T, ((true = isCons T self540)) <-> ((exists tmp203: List T, exists tmp202: T, (Cons_construct T tmp202 tmp203 = self540)))). 
Proof.
	repeat t710 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self541: List T, ((true = isNil T self541)) <-> (((Nil_construct T = self541)))). 
Proof.
	repeat t710 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic67 := match goal with 
	| [ H270: (true = isCons ?T ?self542) |- _ ] => 
			poseNew (Mark (T,self542) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H270)
	| [ H270: (isCons ?T ?self542 = true) |- _ ] => 
			poseNew (Mark (T,self542) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H270))
	| [ H271: (true = isNil ?T ?self543) |- _ ] => 
			poseNew (Mark (T,self543) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H271)
	| [ H271: (isNil ?T ?self543 = true) |- _ ] => 
			poseNew (Mark (T,self543) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H271))
	| _ => Option_tactic67
end.

Ltac t711 :=
  t_base ||
  List_tactic67 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t712 :=
  t711 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t712.

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
Definition content_rt34_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt34_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt34_type T thiss1 := 
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

Ltac rwrtTac_A138 := match goal with 
	| [ H1410: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B138 := match goal with 
	| [ H1410: context[content ?T ?thiss1], H2410: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2410: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac138 := idtac; repeat rwrtTac_A138; repeat rwrtTac_B138.

Ltac t713 :=
  t_base ||
  List_tactic67 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t714 :=
  t713 ||
  rwrtTac138 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t714.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt31_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt31_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt31_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A139 := match goal with 
	| [ H1411: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B139 := match goal with 
	| [ H1411: context[size ?T ?thiss30], H2411: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2411: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac139 := rwrtTac138; repeat rwrtTac_A139; repeat rwrtTac_B139.

Ltac t715 :=
  t_base ||
  List_tactic67 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t716 :=
  t715 ||
  rwrtTac139 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t716.

(***********************
  End of size
 ***********************)

(***********************
  Start of drop
 ***********************)

Obligation Tactic:=idtac.
Definition drop_rt5_type (T: Type) (thiss38: List T) (i: Z) : Type :=
{res8: List T | (ifthenelse (set_subset (content T res8) (content T thiss38)) bool
	(fun _ => Zeq_bool (proj1_sig (size T res8)) (ifthenelse (Z.leb i (0)%Z) Z
		(fun _ => proj1_sig (size T thiss38) )
		(fun _ => ifthenelse (Z.geb i (proj1_sig (size T thiss38))) Z
			(fun _ => (0)%Z )
			(fun _ => Z.sub (proj1_sig (size T thiss38)) i ) )) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold drop_rt5_type.


Equations (noind) drop (T: Type) (thiss38: List T) (i: Z) : drop_rt5_type T thiss38 i := 
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

Ltac rwrtTac_A140 := match goal with 
	| [ H1412: context[drop ?T ?thiss38 ?i] |- _ ] => 
			poseNew (Mark (T,thiss38,i) "unfolding drop_equation")
	| [  |- context[drop ?T ?thiss38 ?i] ] => 
			poseNew (Mark (T,thiss38,i) "unfolding drop_equation")
end.

Ltac rwrtTac_B140 := match goal with 
	| [ H1412: context[drop ?T ?thiss38 ?i], H2412: Marked (?T,?thiss38,?i) "unfolding drop_equation" |- _ ] => 
			poseNew (Mark (T,thiss38,i) "unfolded drop_equation");
			add_equation (drop_equation_1 T thiss38 i)
	| [ H2412: Marked (?T,?thiss38,?i) "unfolding drop_equation" |- context[drop ?T ?thiss38 ?i] ] => 
			poseNew (Mark (T,thiss38,i) "unfolded drop_equation");
			add_equation (drop_equation_1 T thiss38 i)
end.

Ltac rwrtTac140 := rwrtTac139; repeat rwrtTac_A140; repeat rwrtTac_B140.

Ltac t717 :=
  t_base ||
  List_tactic67 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t718 :=
  t717 ||
  rwrtTac140 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t718.

(***********************
  End of drop
 ***********************)

(***********************
  Start of take
 ***********************)

Obligation Tactic:=idtac.
Definition take_rt3_type (T: Type) (thiss61: List T) (i1: Z) : Type :=
{res22: List T | (ifthenelse (set_subset (content T res22) (content T thiss61)) bool
	(fun _ => Zeq_bool (proj1_sig (size T res22)) (ifthenelse (Z.leb i1 (0)%Z) Z
		(fun _ => (0)%Z )
		(fun _ => ifthenelse (Z.geb i1 (proj1_sig (size T thiss61))) Z
			(fun _ => proj1_sig (size T thiss61) )
			(fun _ => i1 ) )) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold take_rt3_type.


Equations (noind) take (T: Type) (thiss61: List T) (i1: Z) : take_rt3_type T thiss61 i1 := 
	take T thiss61 i1 by rec ignore_termination lt :=
	take T thiss61 i1 := ifthenelse (isNil _ thiss61) (List T)
		(fun _ => Nil_construct T )
		(fun _ => ifthenelse (isCons _ thiss61) (List T)
			(fun _ => ifthenelse (Z.leb i1 (0)%Z) (List T)
				(fun _ => Nil_construct T )
				(fun _ => Cons_construct T (h T thiss61) (proj1_sig (take T (t7 T thiss61) (Z.sub i1 (1)%Z))) ) )
			(fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold take_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A141 := match goal with 
	| [ H1413: context[take ?T ?thiss61 ?i1] |- _ ] => 
			poseNew (Mark (T,thiss61,i1) "unfolding take_equation")
	| [  |- context[take ?T ?thiss61 ?i1] ] => 
			poseNew (Mark (T,thiss61,i1) "unfolding take_equation")
end.

Ltac rwrtTac_B141 := match goal with 
	| [ H1413: context[take ?T ?thiss61 ?i1], H2413: Marked (?T,?thiss61,?i1) "unfolding take_equation" |- _ ] => 
			poseNew (Mark (T,thiss61,i1) "unfolded take_equation");
			add_equation (take_equation_1 T thiss61 i1)
	| [ H2413: Marked (?T,?thiss61,?i1) "unfolding take_equation" |- context[take ?T ?thiss61 ?i1] ] => 
			poseNew (Mark (T,thiss61,i1) "unfolded take_equation");
			add_equation (take_equation_1 T thiss61 i1)
end.

Ltac rwrtTac141 := rwrtTac140; repeat rwrtTac_A141; repeat rwrtTac_B141.

Ltac t719 :=
  t_base ||
  List_tactic67 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t720 :=
  t719 ||
  rwrtTac141 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t720.

(***********************
  End of take
 ***********************)


(***********************
  Start of slice
 ***********************)

Definition slice (T: Type) (thiss64: List T) (from1: Z) (to1: Z) (contractHyp215: (ifthenelse
	(ifthenelse (Z.leb (0)%Z from1) bool
		(fun _ => Z.leb from1 to1 )
		(fun _ => false ))
	bool
	(fun _ => Z.leb to1 (proj1_sig (size T thiss64)) )
	(fun _ => false ) = true)) : List T :=
proj1_sig (take T (proj1_sig (drop T thiss64 from1)) (Z.sub to1 from1)).

Fail Next Obligation.

Hint Unfold slice: definitions.

(***********************
  End of slice
 ***********************)
