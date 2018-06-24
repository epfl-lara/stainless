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

Ltac t136 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t137 :=
  t136 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t137.


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

Lemma None_exists: (forall T: Type, forall self136: Option T, ((true = isNone T self136)) <-> (((None_construct T = self136)))). 
Proof.
	repeat t137 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self137: Option T, ((true = isSome T self137)) <-> ((exists tmp51: T, (Some_construct T tmp51 = self137)))). 
Proof.
	repeat t137 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic17 := match goal with 
	| [ H68: (true = isNone ?T ?self138) |- _ ] => 
			poseNew (Mark (T,self138) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H68)
	| [ H68: (isNone ?T ?self138 = true) |- _ ] => 
			poseNew (Mark (T,self138) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H68))
	| [ H69: (true = isSome ?T ?self139) |- _ ] => 
			poseNew (Mark (T,self139) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H69)
	| [ H69: (isSome ?T ?self139 = true) |- _ ] => 
			poseNew (Mark (T,self139) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H69))
	| _ => idtac
end.

Ltac t138 :=
  t_base ||
  Option_tactic17 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t139 :=
  t138 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t139.


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

Lemma Cons_exists: (forall T: Type, forall self140: List T, ((true = isCons T self140)) <-> ((exists tmp53: List T, exists tmp52: T, (Cons_construct T tmp52 tmp53 = self140)))). 
Proof.
	repeat t139 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self141: List T, ((true = isNil T self141)) <-> (((Nil_construct T = self141)))). 
Proof.
	repeat t139 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic17 := match goal with 
	| [ H70: (true = isCons ?T ?self142) |- _ ] => 
			poseNew (Mark (T,self142) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H70)
	| [ H70: (isCons ?T ?self142 = true) |- _ ] => 
			poseNew (Mark (T,self142) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H70))
	| [ H71: (true = isNil ?T ?self143) |- _ ] => 
			poseNew (Mark (T,self143) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H71)
	| [ H71: (isNil ?T ?self143 = true) |- _ ] => 
			poseNew (Mark (T,self143) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H71))
	| _ => Option_tactic17
end.

Ltac t140 :=
  t_base ||
  List_tactic17 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t141 :=
  t140 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t141.

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
  Start of forall
 ***********************)

Obligation Tactic:=idtac.
Definition _forall_rt2_type (T: Type) (thiss8: List T) (p2: T -> bool) : Type :=
bool.

Fail Next Obligation.

Hint Unfold _forall_rt2_type.


Equations (noind) _forall (T: Type) (thiss8: List T) (p2: T -> bool) : _forall_rt2_type T thiss8 p2 := 
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

Ltac rwrtTac_A12 := match goal with 
	| [ H184: context[_forall ?T ?thiss8 ?p2] |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
	| [  |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolding _forall_equation")
end.

Ltac rwrtTac_B12 := match goal with 
	| [ H184: context[_forall ?T ?thiss8 ?p2], H284: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- _ ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
	| [ H284: Marked (?T,?thiss8,?p2) "unfolding _forall_equation" |- context[_forall ?T ?thiss8 ?p2] ] => 
			poseNew (Mark (T,thiss8,p2) "unfolded _forall_equation");
			add_equation (_forall_equation_1 T thiss8 p2)
end.

Ltac rwrtTac12 := idtac; repeat rwrtTac_A12; repeat rwrtTac_B12.

Ltac t142 :=
  t_base ||
  List_tactic17 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t143 :=
  t142 ||
  rwrtTac12 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t143.

(***********************
  End of forall
 ***********************)

(***********************
  Start of exists
 ***********************)

Definition _exists (T: Type) (thiss9: List T) (p3: T -> bool) : bool :=
negb (_forall T thiss9 (fun x___22 => negb (p3 x___22) )).

Fail Next Obligation.

Hint Unfold _exists: definitions.

(***********************
  End of exists
 ***********************)


(***********************
  Start of indexWhere
 ***********************)


Definition indexWhere_rt_type (T: Type) (thiss16: List T) (p6: T -> bool) : Type :=
{x___25: Z | (Bool.eqb (Z.geb x___25 (0)%Z) (_exists T thiss16 p6) = true)}.

Fail Next Obligation.

Hint Unfold indexWhere_rt_type.


Equations (noind) indexWhere (T: Type) (thiss16: List T) (p6: T -> bool) : indexWhere_rt_type T thiss16 p6 := 
	indexWhere T thiss16 p6 by rec ignore_termination lt :=
	indexWhere T thiss16 p6 := ifthenelse (isNil _ thiss16) Z
		(fun _ => (-1)%Z )
		(fun _ => ifthenelse
			(ifthenelse (isCons _ thiss16) bool
				(fun _ => p6 (h T thiss16) )
				(fun _ => false ))
			Z
			(fun _ => (0)%Z )
			(fun _ => ifthenelse (isCons _ thiss16) Z
				(fun _ => let rec1 := (proj1_sig (indexWhere T (t7 T thiss16) p6)) in (ifthenelse (Z.geb rec1 (0)%Z) Z
					(fun _ => Z.add rec1 (1)%Z )
					(fun _ => (-1)%Z )) )
				(fun _ => let contradiction: False := _ in match contradiction with end ) ) ).

Hint Unfold indexWhere_comp_proj.

Solve Obligations with (repeat t143).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A13 := match goal with 
	| [ H185: context[indexWhere ?T ?thiss16 ?p6] |- _ ] => 
			poseNew (Mark (T,thiss16,p6) "unfolding indexWhere_equation")
	| [  |- context[indexWhere ?T ?thiss16 ?p6] ] => 
			poseNew (Mark (T,thiss16,p6) "unfolding indexWhere_equation")
end.

Ltac rwrtTac_B13 := match goal with 
	| [ H185: context[indexWhere ?T ?thiss16 ?p6], H285: Marked (?T,?thiss16,?p6) "unfolding indexWhere_equation" |- _ ] => 
			poseNew (Mark (T,thiss16,p6) "unfolded indexWhere_equation");
			add_equation (indexWhere_equation_1 T thiss16 p6)
	| [ H285: Marked (?T,?thiss16,?p6) "unfolding indexWhere_equation" |- context[indexWhere ?T ?thiss16 ?p6] ] => 
			poseNew (Mark (T,thiss16,p6) "unfolded indexWhere_equation");
			add_equation (indexWhere_equation_1 T thiss16 p6)
end.

Ltac rwrtTac13 := rwrtTac12; repeat rwrtTac_A13; repeat rwrtTac_B13.

Ltac t144 :=
  t_base ||
  List_tactic17 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t145 :=
  t144 ||
  rwrtTac13 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t145.

(***********************
  End of indexWhere
 ***********************)
