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

Ltac t677 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t678 :=
  t677 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t678.


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

Lemma None_exists: (forall T: Type, forall self520: Option T, ((true = isNone T self520)) <-> (((None_construct T = self520)))). 
Proof.
	repeat t678 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self521: Option T, ((true = isSome T self521)) <-> ((exists tmp195: T, (Some_construct T tmp195 = self521)))). 
Proof.
	repeat t678 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic65 := match goal with 
	| [ H260: (true = isNone ?T ?self522) |- _ ] => 
			poseNew (Mark (T,self522) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H260)
	| [ H260: (isNone ?T ?self522 = true) |- _ ] => 
			poseNew (Mark (T,self522) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H260))
	| [ H261: (true = isSome ?T ?self523) |- _ ] => 
			poseNew (Mark (T,self523) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H261)
	| [ H261: (isSome ?T ?self523 = true) |- _ ] => 
			poseNew (Mark (T,self523) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H261))
	| _ => idtac
end.

Ltac t679 :=
  t_base ||
  Option_tactic65 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t680 :=
  t679 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t680.


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

Lemma Cons_exists: (forall T: Type, forall self524: List T, ((true = isCons T self524)) <-> ((exists tmp197: List T, exists tmp196: T, (Cons_construct T tmp196 tmp197 = self524)))). 
Proof.
	repeat t680 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self525: List T, ((true = isNil T self525)) <-> (((Nil_construct T = self525)))). 
Proof.
	repeat t680 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic65 := match goal with 
	| [ H262: (true = isCons ?T ?self526) |- _ ] => 
			poseNew (Mark (T,self526) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H262)
	| [ H262: (isCons ?T ?self526 = true) |- _ ] => 
			poseNew (Mark (T,self526) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H262))
	| [ H263: (true = isNil ?T ?self527) |- _ ] => 
			poseNew (Mark (T,self527) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H263)
	| [ H263: (isNil ?T ?self527 = true) |- _ ] => 
			poseNew (Mark (T,self527) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H263))
	| _ => Option_tactic65
end.

Ltac t681 :=
  t_base ||
  List_tactic65 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t682 :=
  t681 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t682.

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
Definition content_rt32_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt32_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt32_type T thiss1 := 
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

Ltac rwrtTac_A129 := match goal with 
	| [ H1393: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B129 := match goal with 
	| [ H1393: context[content ?T ?thiss1], H2393: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2393: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac129 := idtac; repeat rwrtTac_A129; repeat rwrtTac_B129.

Ltac t683 :=
  t_base ||
  List_tactic65 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t684 :=
  t683 ||
  rwrtTac129 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t684.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt29_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt29_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt29_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A130 := match goal with 
	| [ H1394: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B130 := match goal with 
	| [ H1394: context[size ?T ?thiss30], H2394: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2394: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac130 := rwrtTac129; repeat rwrtTac_A130; repeat rwrtTac_B130.

Ltac t685 :=
  t_base ||
  List_tactic65 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t686 :=
  t685 ||
  rwrtTac130 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t686.

(***********************
  End of size
 ***********************)

(***********************
  Start of drop
 ***********************)

Obligation Tactic:=idtac.
Definition drop_rt3_type (T: Type) (thiss38: List T) (i: Z) : Type :=
{res8: List T | (ifthenelse (set_subset (content T res8) (content T thiss38)) bool
	(fun _ => Zeq_bool (proj1_sig (size T res8)) (ifthenelse (Z.leb i (0)%Z) Z
		(fun _ => proj1_sig (size T thiss38) )
		(fun _ => ifthenelse (Z.geb i (proj1_sig (size T thiss38))) Z
			(fun _ => (0)%Z )
			(fun _ => Z.sub (proj1_sig (size T thiss38)) i ) )) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold drop_rt3_type.


Equations (noind) drop (T: Type) (thiss38: List T) (i: Z) : drop_rt3_type T thiss38 i := 
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

Ltac rwrtTac_A131 := match goal with 
	| [ H1395: context[drop ?T ?thiss38 ?i] |- _ ] => 
			poseNew (Mark (T,thiss38,i) "unfolding drop_equation")
	| [  |- context[drop ?T ?thiss38 ?i] ] => 
			poseNew (Mark (T,thiss38,i) "unfolding drop_equation")
end.

Ltac rwrtTac_B131 := match goal with 
	| [ H1395: context[drop ?T ?thiss38 ?i], H2395: Marked (?T,?thiss38,?i) "unfolding drop_equation" |- _ ] => 
			poseNew (Mark (T,thiss38,i) "unfolded drop_equation");
			add_equation (drop_equation_1 T thiss38 i)
	| [ H2395: Marked (?T,?thiss38,?i) "unfolding drop_equation" |- context[drop ?T ?thiss38 ?i] ] => 
			poseNew (Mark (T,thiss38,i) "unfolded drop_equation");
			add_equation (drop_equation_1 T thiss38 i)
end.

Ltac rwrtTac131 := rwrtTac130; repeat rwrtTac_A131; repeat rwrtTac_B131.

Ltac t687 :=
  t_base ||
  List_tactic65 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t688 :=
  t687 ||
  rwrtTac131 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t688.

(***********************
  End of drop
 ***********************)

(***********************
  Start of take
 ***********************)

Obligation Tactic:=idtac.
Definition take_rt1_type (T: Type) (thiss61: List T) (i1: Z) : Type :=
{res22: List T | (ifthenelse (set_subset (content T res22) (content T thiss61)) bool
	(fun _ => Zeq_bool (proj1_sig (size T res22)) (ifthenelse (Z.leb i1 (0)%Z) Z
		(fun _ => (0)%Z )
		(fun _ => ifthenelse (Z.geb i1 (proj1_sig (size T thiss61))) Z
			(fun _ => proj1_sig (size T thiss61) )
			(fun _ => i1 ) )) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold take_rt1_type.


Equations (noind) take (T: Type) (thiss61: List T) (i1: Z) : take_rt1_type T thiss61 i1 := 
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

Ltac rwrtTac_A132 := match goal with 
	| [ H1396: context[take ?T ?thiss61 ?i1] |- _ ] => 
			poseNew (Mark (T,thiss61,i1) "unfolding take_equation")
	| [  |- context[take ?T ?thiss61 ?i1] ] => 
			poseNew (Mark (T,thiss61,i1) "unfolding take_equation")
end.

Ltac rwrtTac_B132 := match goal with 
	| [ H1396: context[take ?T ?thiss61 ?i1], H2396: Marked (?T,?thiss61,?i1) "unfolding take_equation" |- _ ] => 
			poseNew (Mark (T,thiss61,i1) "unfolded take_equation");
			add_equation (take_equation_1 T thiss61 i1)
	| [ H2396: Marked (?T,?thiss61,?i1) "unfolding take_equation" |- context[take ?T ?thiss61 ?i1] ] => 
			poseNew (Mark (T,thiss61,i1) "unfolded take_equation");
			add_equation (take_equation_1 T thiss61 i1)
end.

Ltac rwrtTac132 := rwrtTac131; repeat rwrtTac_A132; repeat rwrtTac_B132.

Ltac t689 :=
  t_base ||
  List_tactic65 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t690 :=
  t689 ||
  rwrtTac132 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t690.

(***********************
  End of take
 ***********************)


(***********************
  Start of evenSplit
 ***********************)

Definition evenSplit (T: Type) (thiss62: List T) : ((List T) * (List T))%type :=
let c := (Z.div (proj1_sig (size T thiss62)) (2)%Z) in ((proj1_sig (take T thiss62 c),proj1_sig (drop T thiss62 c))).

Fail Next Obligation.

Hint Unfold evenSplit: definitions.

(***********************
  End of evenSplit
 ***********************)
