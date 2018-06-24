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

Ltac t240 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t241 :=
  t240 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t241.


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

Lemma None_exists: (forall T: Type, forall self248: Option T, ((true = isNone T self248)) <-> (((None_construct T = self248)))). 
Proof.
	repeat t241 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self249: Option T, ((true = isSome T self249)) <-> ((exists tmp93: T, (Some_construct T tmp93 = self249)))). 
Proof.
	repeat t241 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic31 := match goal with 
	| [ H124: (true = isNone ?T ?self250) |- _ ] => 
			poseNew (Mark (T,self250) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H124)
	| [ H124: (isNone ?T ?self250 = true) |- _ ] => 
			poseNew (Mark (T,self250) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H124))
	| [ H125: (true = isSome ?T ?self251) |- _ ] => 
			poseNew (Mark (T,self251) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H125)
	| [ H125: (isSome ?T ?self251 = true) |- _ ] => 
			poseNew (Mark (T,self251) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H125))
	| _ => idtac
end.

Ltac t242 :=
  t_base ||
  Option_tactic31 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t243 :=
  t242 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t243.


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

Lemma Cons_exists: (forall T: Type, forall self252: List T, ((true = isCons T self252)) <-> ((exists tmp95: List T, exists tmp94: T, (Cons_construct T tmp94 tmp95 = self252)))). 
Proof.
	repeat t243 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self253: List T, ((true = isNil T self253)) <-> (((Nil_construct T = self253)))). 
Proof.
	repeat t243 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic31 := match goal with 
	| [ H126: (true = isCons ?T ?self254) |- _ ] => 
			poseNew (Mark (T,self254) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H126)
	| [ H126: (isCons ?T ?self254 = true) |- _ ] => 
			poseNew (Mark (T,self254) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H126))
	| [ H127: (true = isNil ?T ?self255) |- _ ] => 
			poseNew (Mark (T,self255) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H127)
	| [ H127: (isNil ?T ?self255 = true) |- _ ] => 
			poseNew (Mark (T,self255) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H127))
	| _ => Option_tactic31
end.

Ltac t244 :=
  t_base ||
  List_tactic31 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t245 :=
  t244 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t245.

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


Definition size_rt_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Solve Obligations with (repeat t245).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A20 := match goal with 
	| [ H1148: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B20 := match goal with 
	| [ H1148: context[size ?T ?thiss30], H2148: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2148: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac20 := idtac; repeat rwrtTac_A20; repeat rwrtTac_B20.

Ltac t247 :=
  t_base ||
  List_tactic31 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t248 :=
  t247 ||
  rwrtTac20 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t248.

(***********************
  End of size
 ***********************)
