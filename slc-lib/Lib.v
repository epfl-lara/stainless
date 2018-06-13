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

Ltac literal b :=
  (unify b true) + (unify b false).

Ltac not_literal b := tryif literal b then fail else idtac.

Ltac rewrite_equations :=
  match goal with
  | U: true = ?b |- _ => not_literal b; apply eq_sym in U
  | U: false = ?b |- _ => not_literal b; apply eq_sym in U
  | U: _ = exist _ _ _ |- _ => rewrite U in *
  | U: exist _ _ _ = _ |- _ => rewrite <- U in *
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

Ltac pose_let a b :=
  poseNew (Mark (a, b) "rewrite_let");  
  (*If only mark for a, we might miss some equations, this way we have useless hypotheses*)
  let A := fresh "A" in
  assert (a = b) as A; [auto | idtac].


Ltac destruct_refinement_aux T :=
  let m := fresh "mres" in
  let r := fresh "r" in
  let cP := fresh "copyP" in
  let P := fresh "P" in
  let MM := fresh "MM" in
  poseNamed MM (Mark T "destruct_refinement");
  pose proof (Mark MM "mark");
  pose proof (proj2_sig T).
(*  define m T;
  autounfold in m;
  destruct m as [ r P ];
  pose proof (Mark P "not_usable");
  pose proof P as cP.                   *)

Ltac no_proj_in T :=
  match T with
  | context[proj1_sig _] => fail 1
  | _ => idtac
  end.

Ltac destruct_refinement :=
  match goal with
  | |- context[proj1_sig ?T] => destruct_refinement_aux T
  | H: context[proj1_sig ?T] |- _ => usable H; destruct_refinement_aux T
  | _ := context[proj1_sig ?T] |- _ => destruct_refinement_aux T
  end.

(* If we have a := b : T in the context, we can pose it *)
Ltac rewrite_let :=
  match goal with
  | H := ?b : ?T |- _ => not_mark b;pose_let H b
  end.


