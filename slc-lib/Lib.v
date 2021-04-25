Require Import Coq.Strings.String.

Require Import Coq.Program.Tactics.
Require Import Coq.Program.Program.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Psatz.

Require Equations.Equations.

Open Scope bool_scope.
Open Scope Z_scope.

Axiom unsupported: False.
Axiom map_type: Type -> Type -> Type.
Axiom ignore_termination: nat.

Definition magic (T: Type): T := match unsupported with end.
Set Default Timeout 60.

Ltac isProp P :=
  let T := type of P in
    unify T Prop.

Inductive Marked {T}: T -> string -> Type :=
  Mark: forall t n, Marked t n.

Open Scope string_scope.

Definition not_usable := "0".
Definition remember := "1".
Definition rewrite_let := "2".
Definition destruct_refinement := "3".
Definition mrk := "4".
Definition instantiation := "5".
Definition split_ite := "6".
Definition constructors := "7".

Opaque not_usable.
Opaque remember.
Opaque rewrite_let.
Opaque destruct_refinement.
Opaque mrk.
Opaque instantiation.
Opaque split_ite.
Opaque constructors.

Ltac duplicate_intro :=
  match goal with
  | |- forall H: ?P, _ =>
    let H := fresh "intro_H" in
    let H2 := fresh "intro_copy" in
    isProp P;
    intros H;
    pose proof (Mark H not_usable);
    pose proof H as H2
  | _ => intros
  end.

Ltac rewrite_everywhere :=
  repeat match goal with
         | H: _ |- _ => rewrite_strat repeat topdown (hints libBool; hints libProp; hints libInts) in H
         end.

Ltac fast :=
  (repeat duplicate_intro) ||
  cbn -[Z.add] in * ||
  subst ||
  (intuition auto) ||
  (progress autorewrite with libBool libProp libInts in * ) ||
(*  (progress rewrite_strat repeat topdown (hints libBool; hints libProp; hints libInts)) ||  *)
(*  rewrite_everywhere || *)
  congruence ||
  discriminate ||
  autounfold in *
.


Ltac slow :=
  lia || nia || ring (*|| eauto.*).

Ltac is_construct t :=
  let x := fresh in
  (let eq := constr:(ltac:(eexists ?[x]; only [x]: econstructor; reflexivity)
    : exists x, x = t) in
  idtac) + fail.

Ltac copy_destruct_exists :=
    match goal with
    |   H: exists x: ?P, _ |- _ =>
        isProp P;
          let x := fresh "ex" x in
          let D := fresh "D" in
          let copyx := fresh "copy_" x in
          let NU := fresh "NU" in
          destruct H as [ x D ];
          pose proof (Mark x not_usable) as NU;
          pose proof x as copyx
    end.


Ltac libStep := match goal with
  | _ => progress fast
  | |- (S ?T <= ?T)%nat =>
    unify T ignore_termination; apply False_ind; exact unsupported
  | _ => copy_destruct_exists
  | [ H: ex _ _ |- _ ] => destruct H
  |   H: exists _, _ |- _ => destruct H
  | H: sig _ |- _ => destruct H
  | H: exist _ _ _ = exist _ _ _ |- _ => inversion H; clear H
  | [ H: ?F _ = ?F _ |- _ ] => is_construct F; inversion H; clear H
  | [ H: ?F _ _ = ?F _ _ |- _ ] => is_construct F; inversion H; clear H
  | [ H: ?F _ _ _ = ?F _ _ _ |- _ ] => is_construct F; inversion H; clear H
  | [ H: ?F _ _ _ _ = ?F _ _ _ _ |- _ ] => is_construct F; inversion H; clear H
  end.

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

Ltac literal b :=
  (unify b true) + (unify b false).

Ltac not_literal b := tryif literal b then fail else idtac.

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
  | H1: Marked H ?n |- _ => unify n not_usable; idtac
  end.

Ltac usable H := not_mark H; tryif not_usable H then fail else idtac.

Ltac define m t :=
  let M := fresh "M" in
  pose t as m;
  assert (t = m) as M; auto;
  pose (Mark M remember).

Ltac pose_let a b :=
  poseNew (Mark (a, b) rewrite_let);
  (*If only mark for a, we might miss some equations, this way we have useless hypotheses*)
  let A := fresh "A" in
  assert (a = b) as A; [auto | idtac].

Ltac destruct_refinement_aux T :=
  let R := fresh "Prp" in
  let MM := fresh "MM" in
  poseNamed MM (Mark T destruct_refinement);
  pose proof (Mark MM mrk);
  pose proof (proj2_sig T) as R.

Ltac destruct_refinement :=
  match goal with
  | |- context[proj1_sig ?T] => destruct_refinement_aux T
  | H: context[proj1_sig ?T] |- _ => usable H; destruct_refinement_aux T
  | H := context[proj1_sig ?T] |- _ => destruct_refinement_aux T
  end.

(* If we have a := b : T in the context, we can pose it *)
Ltac rewrite_let :=
  match goal with
  | H := ?b : ?T |- _ => not_mark b;pose_let H b
  end.

Ltac apply_any :=
  match goal with
  | H: _ |- _ => apply H
  end.

Ltac instantiate_any :=
  match goal with
  | H1: forall x, _ -> _, H2: _ |- _ =>
    poseNew (Mark (H1,H2) instantiation);
    pose proof (H1 _ H2)
  end.
