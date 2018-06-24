Require Import stdpp.set. (* removing this line prevents the problem *)
Require Equations.Equations.
Require Import Coq.Strings.String.

Set Program Mode.

Parameter ignore_termination: nat.
  
Ltac fast :=
  cbn in * ||
  intuition auto ||
  (progress autorewrite with libBool in *) ||
  discriminate
.

Definition ifthenelse b A (e1: true = b -> A) (e2: false = b -> A): A :=
  match b as B return (B = b -> A) with
  | true => fun H => e1 H
  | false => fun H => e2 H
  end eq_refl.

Ltac ifthenelse_step := match goal with
  | [ |- context[ifthenelse ?b _ _ _] ] =>
      let matched := fresh "matched" in
      destruct b eqn:matched
  | [ H: context[ifthenelse ?b _ _ _] |- _ ] =>
      let matched := fresh "matched" in
      destruct b eqn:matched
end.



Lemma if_false_else:
  forall b e2,
           (ifthenelse b bool (fun _ => false) (fun _ => e2)) = true <->
           b = false /\ e2 = true.
Proof.
  intros; repeat fast || ifthenelse_step.
Qed.

Hint Rewrite if_false_else: libBool.
 
Inductive Marked {T}: T -> string -> Type :=
  Mark: forall t s, Marked t s
.

Ltac isThere P :=
  match goal with
  | H: ?Q |- _ => unify P Q
  end.

Ltac termNotThere p :=
  let P := type of p in
  tryif (isThere P) then fail else idtac.

Ltac poseNew E := termNotThere E; pose proof E.
Ltac poseNamed M E := termNotThere E; pose proof E as M.

Ltac not_usable H :=
  match goal with
  | H1: Marked H "not_usable" |- _ => idtac
  end.

Ltac is_mark H :=
  match type of H with
  | Marked _ _ => idtac
  end.

Ltac not_mark H := tryif is_mark H then fail else idtac.

Ltac usable H := not_mark H; tryif not_usable H then fail else idtac.

Ltac define m t :=
  let M := fresh "M" in
  pose t as m;
  assert (t = m) as M; auto;
  pose (Mark M "remembering m").


Ltac destruct_refinement_aux T :=
  let m := fresh "mres" in
  let r := fresh "r" in
  let cP := fresh "copyP" in
  let P := fresh "P" in
  define m T;
  autounfold in m;
  destruct m as [ r P ];
  pose proof (Mark P "not_usable");
  pose proof P as cP.                   

Ltac no_proj_in T :=
  match T with
  | context[proj1_sig _] => fail 1
  | _ => idtac
  end.

Ltac destruct_refinement :=
  match goal with
  | |- context[proj1_sig ?T] => no_proj_in T; destruct_refinement_aux T
  | H: context[proj1_sig ?T] |- _ => no_proj_in T; usable H; destruct_refinement_aux T
  | _ := context[proj1_sig ?T] |- _ => no_proj_in T; destruct_refinement_aux T
  end.


Ltac t_base :=
  fast ||
  destruct_refinement.
 
Obligation Tactic := repeat t_base.

Inductive List (T: Type) :=
| Cons_construct: T -> List T -> List T
| Nil_construct: List T.

Definition Cons_type (T: Type) : Type := { src: List T | False }.
Definition h (T: Type) (src: Cons_type T) : T. Admitted.
Definition t4 (T: Type) (src: Cons_type T) : List T. Admitted.
Definition size (T: Type) (thiss30: List T): {x: nat | True }. Admitted.

Definition filter1_rt1_type (T: Type) (thiss40: List T) (p8: T -> bool) : Type :=
{res10: List T | 
	(ifthenelse (Nat.leb (proj1_sig (size T res10)) 0) bool
		(fun _ => false )
		(fun _ => false ))  = true}.

Fail Next Obligation.

Hint Unfold filter1_rt1_type.

Equations (noind) filter1 (T: Type) (thiss40: List T) (p8: T -> bool) : filter1_rt1_type T thiss40 p8 := 
	filter1 T thiss40 p8 by rec ignore_termination lt :=
	filter1 T thiss40 p8 := ifthenelse false (List T)
		(fun _ => Nil_construct T )
		(fun _ => ifthenelse false
			(List T)
			(fun _ => Nil_construct T)
			(fun _ => proj1_sig (filter1 T (t4 T thiss40) p8) ))
.

Admit Obligations.

Goal
  forall T (p9: T -> bool) (h17: T) (t209: List T) (matched: p9 h17 = true)
      (UUU:
         filter1 T (Nil_construct T) p9 =
         exist
           _
           (ifthenelse (p9 h17) (List T)
             (fun _ => Nil_construct T)
             (fun _ => Nil_construct T))
           (filter1_obligation_3
              T
              (Nil_construct T)
              p9
              (fun (T : Type)
                 (thiss40 : List T)
                 (p8 : T -> bool)
                 (_ : (ignore_termination < ignore_termination)) => filter1 T thiss40 p8))),
    False.
