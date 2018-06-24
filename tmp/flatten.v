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

Ltac t415 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t416 :=
  t415 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t416.


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

Lemma None_exists: (forall T: Type, forall self352: Option T, ((true = isNone T self352)) <-> (((None_construct T = self352)))). 
Proof.
	repeat t416 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self353: Option T, ((true = isSome T self353)) <-> ((exists tmp132: T, (Some_construct T tmp132 = self353)))). 
Proof.
	repeat t416 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic44 := match goal with 
	| [ H176: (true = isNone ?T ?self354) |- _ ] => 
			poseNew (Mark (T,self354) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H176)
	| [ H176: (isNone ?T ?self354 = true) |- _ ] => 
			poseNew (Mark (T,self354) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H176))
	| [ H177: (true = isSome ?T ?self355) |- _ ] => 
			poseNew (Mark (T,self355) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H177)
	| [ H177: (isSome ?T ?self355 = true) |- _ ] => 
			poseNew (Mark (T,self355) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H177))
	| _ => idtac
end.

Ltac t417 :=
  t_base ||
  Option_tactic44 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t418 :=
  t417 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t418.


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

Lemma Cons_exists: (forall T: Type, forall self356: List T, ((true = isCons T self356)) <-> ((exists tmp134: List T, exists tmp133: T, (Cons_construct T tmp133 tmp134 = self356)))). 
Proof.
	repeat t418 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self357: List T, ((true = isNil T self357)) <-> (((Nil_construct T = self357)))). 
Proof.
	repeat t418 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic44 := match goal with 
	| [ H178: (true = isCons ?T ?self358) |- _ ] => 
			poseNew (Mark (T,self358) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H178)
	| [ H178: (isCons ?T ?self358 = true) |- _ ] => 
			poseNew (Mark (T,self358) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H178))
	| [ H179: (true = isNil ?T ?self359) |- _ ] => 
			poseNew (Mark (T,self359) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H179)
	| [ H179: (isNil ?T ?self359 = true) |- _ ] => 
			poseNew (Mark (T,self359) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H179))
	| _ => Option_tactic44
end.

Ltac t419 :=
  t_base ||
  List_tactic44 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t420 :=
  t419 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t420.

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
Definition content_rt17_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt17_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt17_type T thiss1 := 
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

Ltac rwrtTac_A65 := match goal with 
	| [ H1245: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B65 := match goal with 
	| [ H1245: context[content ?T ?thiss1], H2245: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
	| [ H2245: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolded content_equation");
			add_equation (content_equation_1 T thiss1)
end.

Ltac rwrtTac65 := idtac; repeat rwrtTac_A65; repeat rwrtTac_B65.

Ltac t421 :=
  t_base ||
  List_tactic44 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t422 :=
  t421 ||
  rwrtTac65 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t422.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt13_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt13_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt13_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A66 := match goal with 
	| [ H1246: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B66 := match goal with 
	| [ H1246: context[size ?T ?thiss30], H2246: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2246: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac66 := rwrtTac65; repeat rwrtTac_A66; repeat rwrtTac_B66.

Ltac t423 :=
  t_base ||
  List_tactic44 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t424 :=
  t423 ||
  rwrtTac66 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t424.

(***********************
  End of size
 ***********************)

(***********************
  Start of ++
 ***********************)

Obligation Tactic:=idtac.
Definition plus_plus__rt1_type (T: Type) (thiss32: List T) (that1: List T) : Type :=
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

Hint Unfold plus_plus__rt1_type.


Equations (noind) plus_plus_ (T: Type) (thiss32: List T) (that1: List T) : plus_plus__rt1_type T thiss32 that1 := 
	plus_plus_ T thiss32 that1 by rec ignore_termination lt :=
	plus_plus_ T thiss32 that1 := match thiss32 with
	| Nil_construct _ => that1
	| Cons_construct _ x2 xs => Cons_construct T x2 (proj1_sig (plus_plus_ T xs that1))
	end.

Hint Unfold plus_plus__comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A67 := match goal with 
	| [ H1247: context[plus_plus_ ?T ?thiss32 ?that1] |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
	| [  |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
end.

Ltac rwrtTac_B67 := match goal with 
	| [ H1247: context[plus_plus_ ?T ?thiss32 ?that1], H2247: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
	| [ H2247: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			add_equation (plus_plus__equation_1 T thiss32 that1)
end.

Ltac rwrtTac67 := rwrtTac66; repeat rwrtTac_A67; repeat rwrtTac_B67.

Ltac t425 :=
  t_base ||
  List_tactic44 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t426 :=
  t425 ||
  rwrtTac67 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t426.

(***********************
  End of ++
 ***********************)


(***********************
  Start of flatten
 ***********************)


Definition flatten_rt_type (T: Type) (ls: List (List T)) : Type :=
List T.

Fail Next Obligation.

Hint Unfold flatten_rt_type.


Equations (noind) flatten (T: Type) (ls: List (List T)) : flatten_rt_type T ls := 
	flatten T ls by rec ignore_termination lt :=
	flatten T ls := match ls with
	| Cons_construct _ h18 t427 => proj1_sig (plus_plus_ T h18 (flatten T t427))
	| Nil_construct _ => Nil_construct T
	end.

Hint Unfold flatten_comp_proj.

Solve Obligations with (repeat t426).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A68 := match goal with 
	| [ H1248: context[flatten ?T ?ls] |- _ ] => 
			poseNew (Mark (T,ls) "unfolding flatten_equation")
	| [  |- context[flatten ?T ?ls] ] => 
			poseNew (Mark (T,ls) "unfolding flatten_equation")
end.

Ltac rwrtTac_B68 := match goal with 
	| [ H1248: context[flatten ?T ?ls], H2248: Marked (?T,?ls) "unfolding flatten_equation" |- _ ] => 
			poseNew (Mark (T,ls) "unfolded flatten_equation");
			add_equation (flatten_equation_1 T ls)
	| [ H2248: Marked (?T,?ls) "unfolding flatten_equation" |- context[flatten ?T ?ls] ] => 
			poseNew (Mark (T,ls) "unfolded flatten_equation");
			add_equation (flatten_equation_1 T ls)
end.

Ltac rwrtTac68 := rwrtTac67; repeat rwrtTac_A68; repeat rwrtTac_B68.

Ltac t428 :=
  t_base ||
  List_tactic44 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t429 :=
  t428 ||
  rwrtTac68 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t429.

(***********************
  End of flatten
 ***********************)
