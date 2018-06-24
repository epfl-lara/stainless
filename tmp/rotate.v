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

Ltac t691 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t692 :=
  t691 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t692.


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

Lemma None_exists: (forall T: Type, forall self528: Option T, ((true = isNone T self528)) <-> (((None_construct T = self528)))). 
Proof.
	repeat t692 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self529: Option T, ((true = isSome T self529)) <-> ((exists tmp198: T, (Some_construct T tmp198 = self529)))). 
Proof.
	repeat t692 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic66 := match goal with 
	| [ H264: (true = isNone ?T ?self530) |- _ ] => 
			poseNew (Mark (T,self530) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H264)
	| [ H264: (isNone ?T ?self530 = true) |- _ ] => 
			poseNew (Mark (T,self530) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H264))
	| [ H265: (true = isSome ?T ?self531) |- _ ] => 
			poseNew (Mark (T,self531) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H265)
	| [ H265: (isSome ?T ?self531 = true) |- _ ] => 
			poseNew (Mark (T,self531) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H265))
	| _ => idtac
end.

Ltac t693 :=
  t_base ||
  Option_tactic66 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t694 :=
  t693 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t694.


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

Lemma Cons_exists: (forall T: Type, forall self532: List T, ((true = isCons T self532)) <-> ((exists tmp200: List T, exists tmp199: T, (Cons_construct T tmp199 tmp200 = self532)))). 
Proof.
	repeat t694 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self533: List T, ((true = isNil T self533)) <-> (((Nil_construct T = self533)))). 
Proof.
	repeat t694 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic66 := match goal with 
	| [ H266: (true = isCons ?T ?self534) |- _ ] => 
			poseNew (Mark (T,self534) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H266)
	| [ H266: (isCons ?T ?self534 = true) |- _ ] => 
			poseNew (Mark (T,self534) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H266))
	| [ H267: (true = isNil ?T ?self535) |- _ ] => 
			poseNew (Mark (T,self535) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H267)
	| [ H267: (isNil ?T ?self535 = true) |- _ ] => 
			poseNew (Mark (T,self535) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H267))
	| _ => Option_tactic66
end.

Ltac t695 :=
  t_base ||
  List_tactic66 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t696 :=
  t695 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t696.

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
Definition content_rt33_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt33_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt33_type T thiss1 := 
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

Ltac rwrtTac_A133 := match goal with 
	| [ H1401: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B133 := match goal with 
	| [ H1401: context[content ?T ?thiss1], H2401: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2401: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac133 := idtac; repeat rwrtTac_A133; repeat rwrtTac_B133.

Ltac t697 :=
  t_base ||
  List_tactic66 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t698 :=
  t697 ||
  rwrtTac133 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t698.

(***********************
  End of content
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
Definition size_rt30_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt30_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt30_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A134 := match goal with 
	| [ H1402: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B134 := match goal with 
	| [ H1402: context[size ?T ?thiss30], H2402: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2402: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac134 := rwrtTac133; repeat rwrtTac_A134; repeat rwrtTac_B134.

Ltac t699 :=
  t_base ||
  List_tactic66 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t700 :=
  t699 ||
  rwrtTac134 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t700.

(***********************
  End of size
 ***********************)

(***********************
  Start of ++
 ***********************)

Obligation Tactic:=idtac.
Definition plus_plus__rt8_type (T: Type) (thiss32: List T) (that1: List T) : Type :=
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

Hint Unfold plus_plus__rt8_type.


Equations (noind) plus_plus_ (T: Type) (thiss32: List T) (that1: List T) : plus_plus__rt8_type T thiss32 that1 := 
	plus_plus_ T thiss32 that1 by rec ignore_termination lt :=
	plus_plus_ T thiss32 that1 := match thiss32 with
	| Nil_construct _ => that1
	| Cons_construct _ x2 xs => Cons_construct T x2 (proj1_sig (plus_plus_ T xs that1))
	end.

Hint Unfold plus_plus__comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A135 := match goal with 
	| [ H1403: context[plus_plus_ ?T ?thiss32 ?that1] |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
	| [  |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
end.

Ltac rwrtTac_B135 := match goal with 
	| [ H1403: context[plus_plus_ ?T ?thiss32 ?that1], H2403: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
	| [ H2403: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
end.

Ltac rwrtTac135 := rwrtTac134; repeat rwrtTac_A135; repeat rwrtTac_B135.

Ltac t701 :=
  t_base ||
  List_tactic66 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t702 :=
  t701 ||
  rwrtTac135 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t702.

(***********************
  End of ++
 ***********************)

(***********************
  Start of drop
 ***********************)

Obligation Tactic:=idtac.
Definition drop_rt4_type (T: Type) (thiss38: List T) (i: Z) : Type :=
{res8: List T | (ifthenelse (set_subset (content T res8) (content T thiss38)) bool
	(fun _ => Zeq_bool (proj1_sig (size T res8)) (ifthenelse (Z.leb i (0)%Z) Z
		(fun _ => proj1_sig (size T thiss38) )
		(fun _ => ifthenelse (Z.geb i (proj1_sig (size T thiss38))) Z
			(fun _ => (0)%Z )
			(fun _ => Z.sub (proj1_sig (size T thiss38)) i ) )) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold drop_rt4_type.


Equations (noind) drop (T: Type) (thiss38: List T) (i: Z) : drop_rt4_type T thiss38 i := 
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

Ltac rwrtTac_A136 := match goal with 
	| [ H1404: context[drop ?T ?thiss38 ?i] |- _ ] => 
			poseNew (Mark (T,thiss38,i) "unfolding drop_equation")
	| [  |- context[drop ?T ?thiss38 ?i] ] => 
			poseNew (Mark (T,thiss38,i) "unfolding drop_equation")
end.

Ltac rwrtTac_B136 := match goal with 
	| [ H1404: context[drop ?T ?thiss38 ?i], H2404: Marked (?T,?thiss38,?i) "unfolding drop_equation" |- _ ] => 
			poseNew (Mark (T,thiss38,i) "unfolded drop_equation");
			add_equation (drop_equation_1 T thiss38 i)
	| [ H2404: Marked (?T,?thiss38,?i) "unfolding drop_equation" |- context[drop ?T ?thiss38 ?i] ] => 
			poseNew (Mark (T,thiss38,i) "unfolded drop_equation");
			add_equation (drop_equation_1 T thiss38 i)
end.

Ltac rwrtTac136 := rwrtTac135; repeat rwrtTac_A136; repeat rwrtTac_B136.

Ltac t703 :=
  t_base ||
  List_tactic66 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t704 :=
  t703 ||
  rwrtTac136 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t704.

(***********************
  End of drop
 ***********************)

(***********************
  Start of take
 ***********************)

Obligation Tactic:=idtac.
Definition take_rt2_type (T: Type) (thiss61: List T) (i1: Z) : Type :=
{res22: List T | (ifthenelse (set_subset (content T res22) (content T thiss61)) bool
	(fun _ => Zeq_bool (proj1_sig (size T res22)) (ifthenelse (Z.leb i1 (0)%Z) Z
		(fun _ => (0)%Z )
		(fun _ => ifthenelse (Z.geb i1 (proj1_sig (size T thiss61))) Z
			(fun _ => proj1_sig (size T thiss61) )
			(fun _ => i1 ) )) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold take_rt2_type.


Equations (noind) take (T: Type) (thiss61: List T) (i1: Z) : take_rt2_type T thiss61 i1 := 
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

Ltac rwrtTac_A137 := match goal with 
	| [ H1405: context[take ?T ?thiss61 ?i1] |- _ ] => 
			poseNew (Mark (T,thiss61,i1) "unfolding take_equation")
	| [  |- context[take ?T ?thiss61 ?i1] ] => 
			poseNew (Mark (T,thiss61,i1) "unfolding take_equation")
end.

Ltac rwrtTac_B137 := match goal with 
	| [ H1405: context[take ?T ?thiss61 ?i1], H2405: Marked (?T,?thiss61,?i1) "unfolding take_equation" |- _ ] => 
			poseNew (Mark (T,thiss61,i1) "unfolded take_equation");
			add_equation (take_equation_1 T thiss61 i1)
	| [ H2405: Marked (?T,?thiss61,?i1) "unfolding take_equation" |- context[take ?T ?thiss61 ?i1] ] => 
			poseNew (Mark (T,thiss61,i1) "unfolded take_equation");
			add_equation (take_equation_1 T thiss61 i1)
end.

Ltac rwrtTac137 := rwrtTac136; repeat rwrtTac_A137; repeat rwrtTac_B137.

Ltac t705 :=
  t_base ||
  List_tactic66 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t706 :=
  t705 ||
  rwrtTac137 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t706.

(***********************
  End of take
 ***********************)


(***********************
  Start of rotate
 ***********************)

Definition rotate (T: Type) (thiss63: List T) (s3: Z) : {res23: List T | (Zeq_bool (proj1_sig (size T res23)) (proj1_sig (size T thiss63)) = true)} :=
ifthenelse (isEmpty T thiss63) (List T)
	(fun _ => Nil_construct T )
	(fun _ => proj1_sig (plus_plus_ T (proj1_sig (drop T thiss63 (Z.modulo s3 (proj1_sig (size T thiss63))))) (proj1_sig (take T thiss63 (Z.modulo s3 (proj1_sig (size T thiss63)))))) ).

Fail Next Obligation.

Hint Unfold rotate: definitions.

(***********************
  End of rotate
 ***********************)
