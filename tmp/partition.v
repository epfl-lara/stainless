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

Ltac t532 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t533 :=
  t532 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t533.


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

Lemma None_exists: (forall T: Type, forall self424: Option T, ((true = isNone T self424)) <-> (((None_construct T = self424)))). 
Proof.
	repeat t533 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self425: Option T, ((true = isSome T self425)) <-> ((exists tmp159: T, (Some_construct T tmp159 = self425)))). 
Proof.
	repeat t533 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic53 := match goal with 
	| [ H212: (true = isNone ?T ?self426) |- _ ] => 
			poseNew (Mark (T,self426) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H212)
	| [ H212: (isNone ?T ?self426 = true) |- _ ] => 
			poseNew (Mark (T,self426) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H212))
	| [ H213: (true = isSome ?T ?self427) |- _ ] => 
			poseNew (Mark (T,self427) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H213)
	| [ H213: (isSome ?T ?self427 = true) |- _ ] => 
			poseNew (Mark (T,self427) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H213))
	| _ => idtac
end.

Ltac t534 :=
  t_base ||
  Option_tactic53 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t535 :=
  t534 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t535.


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

Lemma Cons_exists: (forall T: Type, forall self428: List T, ((true = isCons T self428)) <-> ((exists tmp161: List T, exists tmp160: T, (Cons_construct T tmp160 tmp161 = self428)))). 
Proof.
	repeat t535 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self429: List T, ((true = isNil T self429)) <-> (((Nil_construct T = self429)))). 
Proof.
	repeat t535 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic53 := match goal with 
	| [ H214: (true = isCons ?T ?self430) |- _ ] => 
			poseNew (Mark (T,self430) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H214)
	| [ H214: (isCons ?T ?self430 = true) |- _ ] => 
			poseNew (Mark (T,self430) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H214))
	| [ H215: (true = isNil ?T ?self431) |- _ ] => 
			poseNew (Mark (T,self431) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H215)
	| [ H215: (isNil ?T ?self431 = true) |- _ ] => 
			poseNew (Mark (T,self431) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H215))
	| _ => Option_tactic53
end.

Ltac t536 :=
  t_base ||
  List_tactic53 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t537 :=
  t536 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t537.

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
  Start of ::
 ***********************)

Definition cons_ (T: Type) (thiss: List T) (t8: T) : List T :=
Cons_construct T t8 thiss.

Fail Next Obligation.

Hint Unfold cons_: definitions.

(***********************
  End of ::
 ***********************)

(***********************
  Start of content
 ***********************)

Obligation Tactic:=idtac.
Definition content_rt24_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt24_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt24_type T thiss1 := 
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

Ltac rwrtTac_A95 := match goal with 
	| [ H1311: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B95 := match goal with 
	| [ H1311: context[content ?T ?thiss1], H2311: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2311: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac95 := idtac; repeat rwrtTac_A95; repeat rwrtTac_B95.

Ltac t538 :=
  t_base ||
  List_tactic53 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t539 :=
  t538 ||
  rwrtTac95 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t539.

(***********************
  End of content
 ***********************)

(***********************
  Start of forall
 ***********************)

Obligation Tactic:=idtac.
Definition _forall_rt6_type (T: Type) (thiss8: List T) (p2: T -> bool) : Type :=
bool.

Fail Next Obligation.

Hint Unfold _forall_rt6_type.


Equations (noind) _forall (T: Type) (thiss8: List T) (p2: T -> bool) : _forall_rt6_type T thiss8 p2 := 
	_forall T thiss8 p2 by rec ignore_termination lt :=
	_forall T thiss8 p2 := match thiss8 with
	| Nil_construct _ => true
	| Cons_construct _ h6 t82 => 
			ifthenelse (p2 h6) bool
				(fun _ => _forall T t82 p2 )
				(fun _ => false )
	end.

Hint Unfold _forall_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A96 := match goal with 
	| [ H1312: context[_forall ?T ?thiss8 ?p2] |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
	| [  |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
end.

Ltac rwrtTac_B96 := match goal with 
	| [ H1312: context[_forall ?T ?thiss8 ?p2], H2312: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
	| [ H2312: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
end.

Ltac rwrtTac96 := rwrtTac95; repeat rwrtTac_A96; repeat rwrtTac_B96.

Ltac t540 :=
  t_base ||
  List_tactic53 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t541 :=
  t540 ||
  rwrtTac96 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t541.

(***********************
  End of forall
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt22_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt22_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt22_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A97 := match goal with 
	| [ H1313: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B97 := match goal with 
	| [ H1313: context[size ?T ?thiss30], H2313: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2313: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac97 := rwrtTac96; repeat rwrtTac_A97; repeat rwrtTac_B97.

Ltac t542 :=
  t_base ||
  List_tactic53 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t543 :=
  t542 ||
  rwrtTac97 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t543.

(***********************
  End of size
 ***********************)

(***********************
  Start of filter
 ***********************)

Obligation Tactic:=idtac.
Definition filter1_rt3_type (T: Type) (thiss40: List T) (p8: T -> bool) : Type :=
{res10: List T | (ifthenelse
	(ifthenelse (Z.leb (proj1_sig (size T res10)) (proj1_sig (size T thiss40))) bool
		(fun _ => set_subset (content T res10) (content T thiss40) )
		(fun _ => false ))
	bool
	(fun _ => _forall T res10 p8 )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold filter1_rt3_type.


Equations (noind) filter1 (T: Type) (thiss40: List T) (p8: T -> bool) : filter1_rt3_type T thiss40 p8 := 
	filter1 T thiss40 p8 by rec ignore_termination lt :=
	filter1 T thiss40 p8 := ifthenelse (isNil _ thiss40) (List T)
		(fun _ => Nil_construct T )
		(fun _ => ifthenelse
			(ifthenelse (isCons _ thiss40) bool
				(fun _ => p8 (h T thiss40) )
				(fun _ => false ))
			(List T)
			(fun _ => Cons_construct T (h T thiss40) (proj1_sig (filter1 T (t7 T thiss40) p8)) )
			(fun _ => ifthenelse (isCons _ thiss40) (List T)
				(fun _ => proj1_sig (filter1 T (t7 T thiss40) p8) )
				(fun _ => let contradiction: False := _ in match contradiction with end ) ) ).

Hint Unfold filter1_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A98 := match goal with 
	| [ H1314: context[filter1 ?T ?thiss40 ?p8] |- _ ] => 
			poseNew (Mark (T,thiss40,p8) "unfolding filter1_equation")
	| [  |- context[filter1 ?T ?thiss40 ?p8] ] => 
			poseNew (Mark (T,thiss40,p8) "unfolding filter1_equation")
end.

Ltac rwrtTac_B98 := match goal with 
	| [ H1314: context[filter1 ?T ?thiss40 ?p8], H2314: Marked (?T,?thiss40,?p8) "unfolding filter1_equation" |- _ ] => 
			poseNew (Mark (T,thiss40,p8) "unfolded filter1_equation");
			add_equation (filter1_equation_1 T thiss40 p8)
	| [ H2314: Marked (?T,?thiss40,?p8) "unfolding filter1_equation" |- context[filter1 ?T ?thiss40 ?p8] ] => 
			poseNew (Mark (T,thiss40,p8) "unfolded filter1_equation");
			add_equation (filter1_equation_1 T thiss40 p8)
end.

Ltac rwrtTac98 := rwrtTac97; repeat rwrtTac_A98; repeat rwrtTac_B98.

Ltac t544 :=
  t_base ||
  List_tactic53 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t545 :=
  t544 ||
  rwrtTac98 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t545.

(***********************
  End of filter
 ***********************)

(***********************
  Start of filterNot
 ***********************)

Definition filterNot (T: Type) (thiss42: List T) (p10: T -> bool) : {res11: List T | (ifthenelse
	(ifthenelse (Z.leb (proj1_sig (size T res11)) (proj1_sig (size T thiss42))) bool
		(fun _ => set_subset (content T res11) (content T thiss42) )
		(fun _ => false ))
	bool
	(fun _ => _forall T res11 (fun x___18 => negb (p10 x___18) ) )
	(fun _ => false ) = true)} :=
proj1_sig (filter1 T thiss42 (fun x___17 => negb (p10 x___17) )).

Fail Next Obligation.

Hint Unfold filterNot: definitions.

(***********************
  End of filterNot
 ***********************)


(***********************
  Start of partition
 ***********************)


Definition partition_rt_type (T: Type) (thiss51: List T) (p11: T -> bool) : Type :=
{res16: ((List T) * (List T))%type | (ifthenelse (propInBool ((fst res16 = proj1_sig (filter1 T thiss51 p11)))) bool
	(fun _ => propInBool ((snd res16 = proj1_sig (filterNot T thiss51 p11))) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold partition_rt_type.


Equations (noind) partition (T: Type) (thiss51: List T) (p11: T -> bool) : partition_rt_type T thiss51 p11 := 
	partition T thiss51 p11 by rec ignore_termination lt :=
	partition T thiss51 p11 := match thiss51 with
	| Nil_construct _ => (Nil_construct T,Nil_construct T)
	| Cons_construct _ h21 t546 => 
			let x___19 := ((fst (proj1_sig (partition T t546 p11)),snd (proj1_sig (partition T t546 p11)))) in (let l2 := (snd x___19) in (ifthenelse (p11 h21) (((List T) * (List T))%type)
				(fun _ => (cons_ T (fst x___19) h21,l2) )
				(fun _ => (fst x___19,cons_ T l2 h21) )))
	end.

Hint Unfold partition_comp_proj.

Solve Obligations with (repeat t545).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A99 := match goal with 
	| [ H1315: context[partition ?T ?thiss51 ?p11] |- _ ] => 
			poseNew (Mark (T,thiss51,p11) "unfolding partition_equation")
	| [  |- context[partition ?T ?thiss51 ?p11] ] => 
			poseNew (Mark (T,thiss51,p11) "unfolding partition_equation")
end.

Ltac rwrtTac_B99 := match goal with 
	| [ H1315: context[partition ?T ?thiss51 ?p11], H2315: Marked (?T,?thiss51,?p11) "unfolding partition_equation" |- _ ] => 
			poseNew (Mark (T,thiss51,p11) "unfolded partition_equation");
			add_equation (partition_equation_1 T thiss51 p11)
	| [ H2315: Marked (?T,?thiss51,?p11) "unfolding partition_equation" |- context[partition ?T ?thiss51 ?p11] ] => 
			poseNew (Mark (T,thiss51,p11) "unfolded partition_equation");
			add_equation (partition_equation_1 T thiss51 p11)
end.

Ltac rwrtTac99 := rwrtTac98; repeat rwrtTac_A99; repeat rwrtTac_B99.

Ltac t547 :=
  t_base ||
  List_tactic53 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t548 :=
  t547 ||
  rwrtTac99 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t548.

(***********************
  End of partition
 ***********************)
