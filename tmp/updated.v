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

Ltac t782 :=
  t_base ||
  idtac ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t783 :=
  t782 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t783.


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

Lemma None_exists: (forall T: Type, forall self584: Option T, ((true = isNone T self584)) <-> (((None_construct T = self584)))). 
Proof.
	repeat t783 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self585: Option T, ((true = isSome T self585)) <-> ((exists tmp219: T, (Some_construct T tmp219 = self585)))). 
Proof.
	repeat t783 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic73 := match goal with 
	| [ H292: (true = isNone ?T ?self586) |- _ ] => 
			poseNew (Mark (T,self586) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H292)
	| [ H292: (isNone ?T ?self586 = true) |- _ ] => 
			poseNew (Mark (T,self586) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H292))
	| [ H293: (true = isSome ?T ?self587) |- _ ] => 
			poseNew (Mark (T,self587) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H293)
	| [ H293: (isSome ?T ?self587 = true) |- _ ] => 
			poseNew (Mark (T,self587) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H293))
	| _ => idtac
end.

Ltac t784 :=
  t_base ||
  Option_tactic73 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t785 :=
  t784 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t785.


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

Lemma Cons_exists: (forall T: Type, forall self588: List T, ((true = isCons T self588)) <-> ((exists tmp221: List T, exists tmp220: T, (Cons_construct T tmp220 tmp221 = self588)))). 
Proof.
	repeat t785 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self589: List T, ((true = isNil T self589)) <-> (((Nil_construct T = self589)))). 
Proof.
	repeat t785 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic73 := match goal with 
	| [ H294: (true = isCons ?T ?self590) |- _ ] => 
			poseNew (Mark (T,self590) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H294)
	| [ H294: (isCons ?T ?self590 = true) |- _ ] => 
			poseNew (Mark (T,self590) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H294))
	| [ H295: (true = isNil ?T ?self591) |- _ ] => 
			poseNew (Mark (T,self591) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H295)
	| [ H295: (isNil ?T ?self591 = true) |- _ ] => 
			poseNew (Mark (T,self591) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H295))
	| _ => Option_tactic73
end.

Ltac t786 :=
  t_base ||
  List_tactic73 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t787 :=
  t786 ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t787.

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
Definition size_rt35_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt35_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt35_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t246 => Z.add (1)%Z (proj1_sig (size T t246))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A157 := match goal with 
	| [ H1453: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B157 := match goal with 
	| [ H1453: context[size ?T ?thiss30], H2453: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
	| [ H2453: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolded size_equation");
			add_equation (size_equation_1 T thiss30)
end.

Ltac rwrtTac157 := idtac; repeat rwrtTac_A157; repeat rwrtTac_B157.

Ltac t788 :=
  t_base ||
  List_tactic73 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t789 :=
  t788 ||
  rwrtTac157 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t789.

(***********************
  End of size
 ***********************)


(***********************
  Start of updated
 ***********************)


Definition contractHyp234_type (T: Type) (thiss70: List T) (i2: Z) (y: T) : Type :=
(ifthenelse (Z.leb (0)%Z i2) bool
	(fun _ => Z.ltb i2 (proj1_sig (size T thiss70)) )
	(fun _ => false ) = true).

Fail Next Obligation.

Hint Unfold contractHyp234_type.


Definition updated_rt_type (T: Type) (thiss70: List T) (i2: Z) (y: T) (contractHyp234: contractHyp234_type T thiss70 i2 y) : Type :=
List T.

Fail Next Obligation.

Hint Unfold updated_rt_type.


Equations (noind) updated (T: Type) (thiss70: List T) (i2: Z) (y: T) (contractHyp234: contractHyp234_type T thiss70 i2 y) : updated_rt_type T thiss70 i2 y contractHyp234 := 
	updated T thiss70 i2 y contractHyp234 by rec ignore_termination lt :=
	updated T thiss70 i2 y contractHyp234 := ifthenelse
		(ifthenelse (isCons _ thiss70) bool
			(fun _ => Zeq_bool i2 (0)%Z )
			(fun _ => false ))
		(List T)
		(fun _ => Cons_construct T y (t7 T thiss70) )
		(fun _ => ifthenelse (isCons _ thiss70) (List T)
			(fun _ => Cons_construct T (h T thiss70) (updated T (t7 T thiss70) (Z.sub i2 (1)%Z) y _) )
			(fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold updated_comp_proj.

Solve Obligations with (repeat t789).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A158 := match goal with 
	| [ H1454: context[updated ?T ?thiss70 ?i2 ?y] |- _ ] => 
			poseNew (Mark (T,thiss70,i2,y) "unfolding updated_equation")
	| [  |- context[updated ?T ?thiss70 ?i2 ?y] ] => 
			poseNew (Mark (T,thiss70,i2,y) "unfolding updated_equation")
end.

Ltac rwrtTac_B158 := match goal with 
	| [ H1454: context[updated ?T ?thiss70 ?i2 ?y], H2454: Marked (?T,?thiss70,?i2,?y) "unfolding updated_equation" |- _ ] => 
			poseNew (Mark (T,thiss70,i2,y) "unfolded updated_equation");
			add_equation (updated_equation_1 T thiss70 i2 y)
	| [ H2454: Marked (?T,?thiss70,?i2,?y) "unfolding updated_equation" |- context[updated ?T ?thiss70 ?i2 ?y] ] => 
			poseNew (Mark (T,thiss70,i2,y) "unfolded updated_equation");
			add_equation (updated_equation_1 T thiss70 i2 y)
end.

Ltac rwrtTac158 := rwrtTac157; repeat rwrtTac_A158; repeat rwrtTac_B158.

Ltac t790 :=
  t_base ||
  List_tactic73 ||
  slow ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in *.
Ltac t791 :=
  t790 ||
  rwrtTac158 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t791.

(***********************
  End of updated
 ***********************)
