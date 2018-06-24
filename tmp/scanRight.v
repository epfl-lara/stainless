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

Ltac t231 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t232 :=
  t231 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t232.


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

Lemma None_exists: (forall T: Type, forall self240: Option T, ((true = isNone T self240)) <-> (((None_construct T = self240)))). 
Proof.
	repeat t232 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self241: Option T, ((true = isSome T self241)) <-> ((exists tmp90: T, (Some_construct T tmp90 = self241)))). 
Proof.
	repeat t232 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic30 := match goal with 
	| [ H120: (true = isNone ?T ?self242) |- _ ] => 
			poseNew (Mark (T,self242) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H120)
	| [ H120: (isNone ?T ?self242 = true) |- _ ] => 
			poseNew (Mark (T,self242) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H120))
	| [ H121: (true = isSome ?T ?self243) |- _ ] => 
			poseNew (Mark (T,self243) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H121)
	| [ H121: (isSome ?T ?self243 = true) |- _ ] => 
			poseNew (Mark (T,self243) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H121))
	| _ => idtac
end.

Ltac t233 :=
  t_base ||
  Option_tactic30 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t234 :=
  t233 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t234.


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

Lemma Cons_exists: (forall T: Type, forall self244: List T, ((true = isCons T self244)) <-> ((exists tmp92: List T, exists tmp91: T, (Cons_construct T tmp91 tmp92 = self244)))). 
Proof.
	repeat t234 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self245: List T, ((true = isNil T self245)) <-> (((Nil_construct T = self245)))). 
Proof.
	repeat t234 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic30 := match goal with 
	| [ H122: (true = isCons ?T ?self246) |- _ ] => 
			poseNew (Mark (T,self246) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H122)
	| [ H122: (isCons ?T ?self246 = true) |- _ ] => 
			poseNew (Mark (T,self246) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H122))
	| [ H123: (true = isNil ?T ?self247) |- _ ] => 
			poseNew (Mark (T,self247) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H123)
	| [ H123: (isNil ?T ?self247 = true) |- _ ] => 
			poseNew (Mark (T,self247) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H123))
	| _ => Option_tactic30
end.

Ltac t235 :=
  t_base ||
  List_tactic30 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t236 :=
  t235 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t236.

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
  Start of scanRight
 ***********************)


Definition scanRight_rt_type (T: Type) (R: Type) (thiss29: List T) (z3: R) (f6: T -> (R -> R)) : Type :=
{x___16: List R | (negb (isEmpty R x___16) = true)}.

Fail Next Obligation.

Hint Unfold scanRight_rt_type.


Equations (noind) scanRight (T: Type) (R: Type) (thiss29: List T) (z3: R) (f6: T -> (R -> R)) : scanRight_rt_type T R thiss29 z3 f6 := 
	scanRight T R thiss29 z3 f6 by rec ignore_termination lt :=
	scanRight T R thiss29 z3 f6 := match thiss29 with
	| Nil_construct _ => cons_ R (Nil_construct R) z3
	| Cons_construct _ h11 t237 => 
			let x___14 := (ifthenelse (isCons _ (proj1_sig (scanRight T R t237 z3 f6))) (((List R) * R)%type)
				(fun _ => (proj1_sig (scanRight T R t237 z3 f6),h R (proj1_sig (scanRight T R t237 z3 f6))) )
				(fun _ => let contradiction: False := _ in match contradiction with end )) in (let h1 := (snd x___14) in (let x___15 := (f6 h11 h1) in (cons_ R (fst x___14) x___15)))
	end.

Hint Unfold scanRight_comp_proj.

Solve Obligations with (repeat t236).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A19 := match goal with 
	| [ H1143: context[scanRight ?T ?R ?thiss29 ?z3 ?f6] |- _ ] => 
			poseNew (Mark (T,R,thiss29,z3,f6) "unfolding scanRight_equation")
	| [  |- context[scanRight ?T ?R ?thiss29 ?z3 ?f6] ] => 
			poseNew (Mark (T,R,thiss29,z3,f6) "unfolding scanRight_equation")
end.

Ltac rwrtTac_B19 := match goal with 
	| [ H1143: context[scanRight ?T ?R ?thiss29 ?z3 ?f6], H2143: Marked (?T,?R,?thiss29,?z3,?f6) "unfolding scanRight_equation" |- _ ] => 
			poseNew (Mark (T,R,thiss29,z3,f6) "unfolded scanRight_equation");
			add_equation (scanRight_equation_1 T R thiss29 z3 f6)
	| [ H2143: Marked (?T,?R,?thiss29,?z3,?f6) "unfolding scanRight_equation" |- context[scanRight ?T ?R ?thiss29 ?z3 ?f6] ] => 
			poseNew (Mark (T,R,thiss29,z3,f6) "unfolded scanRight_equation");
			add_equation (scanRight_equation_1 T R thiss29 z3 f6)
end.

Ltac rwrtTac19 := idtac; repeat rwrtTac_A19; repeat rwrtTac_B19.

Ltac t238 :=
  t_base ||
  List_tactic30 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t239 :=
  t238 ||
  rwrtTac19 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t239.

(***********************
  End of scanRight
 ***********************)
