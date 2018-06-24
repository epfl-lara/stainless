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

Ltac t721 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t722 :=
  t721 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t722.


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

Lemma None_exists: (forall T: Type, forall self544: Option T, ((true = isNone T self544)) <-> (((None_construct T = self544)))). 
Proof.
	repeat t722 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self545: Option T, ((true = isSome T self545)) <-> ((exists tmp204: T, (Some_construct T tmp204 = self545)))). 
Proof.
	repeat t722 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic68 := match goal with 
	| [ H272: (true = isNone ?T ?self546) |- _ ] => 
			poseNew (Mark (T,self546) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H272)
	| [ H272: (isNone ?T ?self546 = true) |- _ ] => 
			poseNew (Mark (T,self546) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H272))
	| [ H273: (true = isSome ?T ?self547) |- _ ] => 
			poseNew (Mark (T,self547) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H273)
	| [ H273: (isSome ?T ?self547 = true) |- _ ] => 
			poseNew (Mark (T,self547) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H273))
	| _ => idtac
end.

Ltac t723 :=
  t_base ||
  Option_tactic68 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t724 :=
  t723 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t724.


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

Lemma Cons_exists: (forall T: Type, forall self548: List T, ((true = isCons T self548)) <-> ((exists tmp206: List T, exists tmp205: T, (Cons_construct T tmp205 tmp206 = self548)))). 
Proof.
	repeat t724 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self549: List T, ((true = isNil T self549)) <-> (((Nil_construct T = self549)))). 
Proof.
	repeat t724 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic68 := match goal with 
	| [ H274: (true = isCons ?T ?self550) |- _ ] => 
			poseNew (Mark (T,self550) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H274)
	| [ H274: (isCons ?T ?self550 = true) |- _ ] => 
			poseNew (Mark (T,self550) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H274))
	| [ H275: (true = isNil ?T ?self551) |- _ ] => 
			poseNew (Mark (T,self551) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H275)
	| [ H275: (isNil ?T ?self551 = true) |- _ ] => 
			poseNew (Mark (T,self551) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H275))
	| _ => Option_tactic68
end.

Ltac t725 :=
  t_base ||
  List_tactic68 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t726 :=
  t725 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t726.

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
Definition content_rt35_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt35_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt35_type T thiss1 := 
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

Ltac rwrtTac_A142 := match goal with 
	| [ H1418: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B142 := match goal with 
	| [ H1418: context[content ?T ?thiss1], H2418: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2418: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac142 := idtac; repeat rwrtTac_A142; repeat rwrtTac_B142.

Ltac t727 :=
  t_base ||
  List_tactic68 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t728 :=
  t727 ||
  rwrtTac142 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t728.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt32_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt32_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt32_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A143 := match goal with 
	| [ H1419: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B143 := match goal with 
	| [ H1419: context[size ?T ?thiss30], H2419: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2419: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac143 := rwrtTac142; repeat rwrtTac_A143; repeat rwrtTac_B143.

Ltac t729 :=
  t_base ||
  List_tactic68 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t730 :=
  t729 ||
  rwrtTac143 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t730.

(***********************
  End of size
 ***********************)

(***********************
  Start of ++
 ***********************)

Obligation Tactic:=idtac.
Definition plus_plus__rt9_type (T: Type) (thiss32: List T) (that1: List T) : Type :=
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

Hint Unfold plus_plus__rt9_type.


Equations (noind) plus_plus_ (T: Type) (thiss32: List T) (that1: List T) : plus_plus__rt9_type T thiss32 that1 := 
	plus_plus_ T thiss32 that1 by rec ignore_termination lt :=
	plus_plus_ T thiss32 that1 := match thiss32 with
	| Nil_construct _ => that1
	| Cons_construct _ x2 xs => Cons_construct T x2 (proj1_sig (plus_plus_ T xs that1))
	end.

Hint Unfold plus_plus__comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A144 := match goal with 
	| [ H1420: context[plus_plus_ ?T ?thiss32 ?that1] |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
	| [  |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
end.

Ltac rwrtTac_B144 := match goal with 
	| [ H1420: context[plus_plus_ ?T ?thiss32 ?that1], H2420: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
	| [ H2420: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
end.

Ltac rwrtTac144 := rwrtTac143; repeat rwrtTac_A144; repeat rwrtTac_B144.

Ltac t731 :=
  t_base ||
  List_tactic68 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t732 :=
  t731 ||
  rwrtTac144 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t732.

(***********************
  End of ++
 ***********************)

(***********************
  Start of drop
 ***********************)

Obligation Tactic:=idtac.
Definition drop_rt6_type (T: Type) (thiss38: List T) (i: Z) : Type :=
{res8: List T | (ifthenelse (set_subset (content T res8) (content T thiss38)) bool
	(fun _ => Zeq_bool (proj1_sig (size T res8)) (ifthenelse (Z.leb i (0)%Z) Z
		(fun _ => proj1_sig (size T thiss38) )
		(fun _ => ifthenelse (Z.geb i (proj1_sig (size T thiss38))) Z
			(fun _ => (0)%Z )
			(fun _ => Z.sub (proj1_sig (size T thiss38)) i ) )) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold drop_rt6_type.


Equations (noind) drop (T: Type) (thiss38: List T) (i: Z) : drop_rt6_type T thiss38 i := 
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

Ltac rwrtTac_A145 := match goal with 
	| [ H1421: context[drop ?T ?thiss38 ?i] |- _ ] => 
			poseNew (Mark (T,thiss38,i) "unfolding drop_equation")
	| [  |- context[drop ?T ?thiss38 ?i] ] => 
			poseNew (Mark (T,thiss38,i) "unfolding drop_equation")
end.

Ltac rwrtTac_B145 := match goal with 
	| [ H1421: context[drop ?T ?thiss38 ?i], H2421: Marked (?T,?thiss38,?i) "unfolding drop_equation" |- _ ] => 
			poseNew (Mark (T,thiss38,i) "unfolded drop_equation");
			add_equation (drop_equation_1 T thiss38 i)
	| [ H2421: Marked (?T,?thiss38,?i) "unfolding drop_equation" |- context[drop ?T ?thiss38 ?i] ] => 
			poseNew (Mark (T,thiss38,i) "unfolded drop_equation");
			add_equation (drop_equation_1 T thiss38 i)
end.

Ltac rwrtTac145 := rwrtTac144; repeat rwrtTac_A145; repeat rwrtTac_B145.

Ltac t733 :=
  t_base ||
  List_tactic68 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t734 :=
  t733 ||
  rwrtTac145 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t734.

(***********************
  End of drop
 ***********************)

(***********************
  Start of take
 ***********************)

Obligation Tactic:=idtac.
Definition take_rt4_type (T: Type) (thiss61: List T) (i1: Z) : Type :=
{res22: List T | (ifthenelse (set_subset (content T res22) (content T thiss61)) bool
	(fun _ => Zeq_bool (proj1_sig (size T res22)) (ifthenelse (Z.leb i1 (0)%Z) Z
		(fun _ => (0)%Z )
		(fun _ => ifthenelse (Z.geb i1 (proj1_sig (size T thiss61))) Z
			(fun _ => proj1_sig (size T thiss61) )
			(fun _ => i1 ) )) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold take_rt4_type.


Equations (noind) take (T: Type) (thiss61: List T) (i1: Z) : take_rt4_type T thiss61 i1 := 
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

Ltac rwrtTac_A146 := match goal with 
	| [ H1422: context[take ?T ?thiss61 ?i1] |- _ ] => 
			poseNew (Mark (T,thiss61,i1) "unfolding take_equation")
	| [  |- context[take ?T ?thiss61 ?i1] ] => 
			poseNew (Mark (T,thiss61,i1) "unfolding take_equation")
end.

Ltac rwrtTac_B146 := match goal with 
	| [ H1422: context[take ?T ?thiss61 ?i1], H2422: Marked (?T,?thiss61,?i1) "unfolding take_equation" |- _ ] => 
			poseNew (Mark (T,thiss61,i1) "unfolded take_equation");
			add_equation (take_equation_1 T thiss61 i1)
	| [ H2422: Marked (?T,?thiss61,?i1) "unfolding take_equation" |- context[take ?T ?thiss61 ?i1] ] => 
			poseNew (Mark (T,thiss61,i1) "unfolded take_equation");
			add_equation (take_equation_1 T thiss61 i1)
end.

Ltac rwrtTac146 := rwrtTac145; repeat rwrtTac_A146; repeat rwrtTac_B146.

Ltac t735 :=
  t_base ||
  List_tactic68 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t736 :=
  t735 ||
  rwrtTac146 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t736.

(***********************
  End of take
 ***********************)


(***********************
  Start of splitAtIndex
 ***********************)


Definition splitAtIndex_rt_type (T: Type) (thiss65: List T) (index1: Z) : Type :=
{res24: ((List T) * (List T))%type | (ifthenelse
	(ifthenelse (propInBool ((proj1_sig (plus_plus_ T (fst res24) (snd res24)) = thiss65))) bool
		(fun _ => propInBool ((fst res24 = proj1_sig (take T thiss65 index1))) )
		(fun _ => false ))
	bool
	(fun _ => propInBool ((snd res24 = proj1_sig (drop T thiss65 index1))) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold splitAtIndex_rt_type.


Equations (noind) splitAtIndex (T: Type) (thiss65: List T) (index1: Z) : splitAtIndex_rt_type T thiss65 index1 := 
	splitAtIndex T thiss65 index1 by rec ignore_termination lt :=
	splitAtIndex T thiss65 index1 := match thiss65 with
	| Nil_construct _ => (Nil_construct T,Nil_construct T)
	| Cons_construct _ h26 rest1 => 
			ifthenelse (Z.leb index1 (0)%Z) (((List T) * (List T))%type)
				(fun _ => (Nil_construct T,thiss65) )
				(fun _ => let x___7 := ((fst (proj1_sig (splitAtIndex T rest1 (Z.sub index1 (1)%Z))),snd (proj1_sig (splitAtIndex T rest1 (Z.sub index1 (1)%Z))))) in (let right := (snd x___7) in ((Cons_construct T h26 (fst x___7),right))) )
	end.

Hint Unfold splitAtIndex_comp_proj.

Solve Obligations with (repeat t736).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A147 := match goal with 
	| [ H1423: context[splitAtIndex ?T ?thiss65 ?index1] |- _ ] => 
			poseNew (Mark (T,thiss65,index1) "unfolding splitAtIndex_equation")
	| [  |- context[splitAtIndex ?T ?thiss65 ?index1] ] => 
			poseNew (Mark (T,thiss65,index1) "unfolding splitAtIndex_equation")
end.

Ltac rwrtTac_B147 := match goal with 
	| [ H1423: context[splitAtIndex ?T ?thiss65 ?index1], H2423: Marked (?T,?thiss65,?index1) "unfolding splitAtIndex_equation" |- _ ] => 
			poseNew (Mark (T,thiss65,index1) "unfolded splitAtIndex_equation");
			add_equation (splitAtIndex_equation_1 T thiss65 index1)
	| [ H2423: Marked (?T,?thiss65,?index1) "unfolding splitAtIndex_equation" |- context[splitAtIndex ?T ?thiss65 ?index1] ] => 
			poseNew (Mark (T,thiss65,index1) "unfolded splitAtIndex_equation");
			add_equation (splitAtIndex_equation_1 T thiss65 index1)
end.

Ltac rwrtTac147 := rwrtTac146; repeat rwrtTac_A147; repeat rwrtTac_B147.

Ltac t737 :=
  t_base ||
  List_tactic68 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t738 :=
  t737 ||
  rwrtTac147 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t738.

(***********************
  End of splitAtIndex
 ***********************)
