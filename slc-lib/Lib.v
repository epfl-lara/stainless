Require Import Coq.Program.Tactics.
Require Import Coq.Program.Program.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Omega.
Require Import ZArith.
Require Import stdpp.set.

Require Equations.Equations.

Open Scope bool_scope.
Open Scope Z_scope.

Axiom unsupported: False. 
Axiom map_type: Type -> Type -> Type.
Axiom ignore_termination: nat.

Definition magic (T: Type): T := match unsupported with end.
Set Default Timeout 60.

  
Ltac fast :=
  intros ||
  cbn -[Z.add] in * ||
  subst ||
  intuition ||
  (progress autorewrite with libInts in *) ||
  (progress autorewrite with libProp in *) ||
  (progress autorewrite with libBool in *) ||
  congruence ||
  discriminate ||
  done ||
  autounfold in *
.

Ltac slow :=
  omega || ring (*|| eauto.*).

Ltac libStep := match goal with
  | _ => progress fast
  | |- (S ?T <= ?T)%nat =>
    unify T ignore_termination; apply False_ind; exact unsupported
  | [ H: ex _ _ |- _ ] => destruct H
  |   H: exists _, _ |- _ => destruct H
  | H: sig _ |- _ => destruct H
  | H: exist _ _ _ = exist _ _ _ |- _ => inversion H; clear H
  end.
  


Inductive Marked {T}: T -> string -> Type :=
  Mark: forall t s, Marked t s
.

(* Notation "'internal'" := (Marked _ _) (at level 50). *)

Ltac clearMarked :=
  repeat match goal with
         | H: Marked _ _ |- _ => clear H
         end.

Ltac clearUseless :=
  repeat match goal with
         | H: ?t = ?t |- _ => clear H
         | _ => clearMarked
         end.

Ltac isThere P :=
  match goal with
  | H: ?Q |- _ => unify P Q
  end.

Ltac isNotMatch  M :=
  match M with
  | match _ with _ => _ end => fail 1
  | match _ with _ => _ end _ => fail 1
  | _ => idtac
  end.

Ltac rewrite_equations :=
  match goal with
  | U: _ = exist _ _ _ |- _ => rewrite U in *
  | U: exist _ _ _ = _ |- _ => rewrite <- U in *
  | U: _ = ?E |- _ => 
      match goal with
      | H: Marked U "equation" |- _ => isNotMatch E; rewrite U in *  
      end
  end.

Ltac termNotThere p :=
  let P := type of p in
  tryif (isThere P) then fail else idtac.


Ltac poseNew E := termNotThere E; pose proof E.
Ltac poseNamed M E := termNotThere E; pose proof E as M.


Ltac program_simplify :=
  cbn -[Z.add]; intros ; destruct_all_rec_calls ; repeat (destruct_conjs; simpl proj1_sig in * );
  subst*; autoinjections ; try discriminates ;
  try (solve [ red ; intros ; destruct_conjs ; autoinjections ; discriminates ]).

Ltac program_simpl := program_simplify ; try typeclasses eauto with program ; try program_solve_wf.


Ltac is_mark H :=
  match type of H with
  | Marked _ _ => idtac
  end.

Ltac not_mark H := tryif is_mark H then fail else idtac.

Ltac not_usable H :=
  match goal with
  | H1: Marked H "not_usable" |- _ => idtac
  end.

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
  let MM := fresh "MM" in
  poseNamed MM (Mark T "destruct_refinement");
  pose proof (Mark MM "mark");
  define m T;
  autounfold in m;
  destruct m as [ r P ];
  pose proof (Mark P "not_usable");
  pose proof P as cP.                   

Ltac destruct_refinement :=
  match goal with
  | |- context[proj1_sig ?T] => destruct_refinement_aux T
  | H: context[proj1_sig ?T] |- _ => usable H; destruct_refinement_aux T
  end.


