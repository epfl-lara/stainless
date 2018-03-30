Require Import Coq.Program.Tactics.
Require Import Coq.Program.Program.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Logic.Classical.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Omega.
Require Import ZArith.

Open Scope bool_scope.
Open Scope Z_scope.

Axiom classicT: forall P: Prop, P + ~P.
Axiom unsupported: False. 
Axiom map_type: Type -> Type -> Type.
Axiom ignore_termination: nat.

Definition propInBool (P: Prop): bool :=
 if (classicT P)
 then true
 else false.

Hint Unfold propInBool.

Lemma Aeq_dec_all: forall T: Type, forall x y: T, {x = y} + {x <> y}.
  intros.
  pose proof classicT (x  = y) as H.
  destruct H; intuition.
Qed.


Definition ifthenelse b A (e1: true =b -> A) (e2: false = b -> A): A :=
  match b as B return (B = b -> A) with
  | true => fun H => e1 H
  | false => fun H => e2 H
  end eq_refl.

Definition set_subset {T: Type} (a b: set T): bool :=
  propInBool ((set_diff (Aeq_dec_all _) a b) = empty_set T).

Definition magic (T: Type): T := match unsupported with end.
Set Default Timeout 60.

Notation "'if' '(' b ')' '{' T '}' 'then' '{' p1 '}' e1 'else' '{' p2 '}' e2" :=
  (ifthenelse b T (fun p1 => e1) (fun p2 => e2)) (at level 80).
Notation "'if' '(' b ')' '{' T '}' 'then' e1 'else' e2" :=
  (ifthenelse b T (fun _ => e1) (fun _ => e2)) (at level 80).
  
Ltac easy :=
  congruence ||
  cbn -[Z.add] in * ||
  intuition ||
  omega ||
  ring ||
  eauto ||
  discriminate ||
  autorewrite with libR in *.

Ltac libStep := match goal with
  | _ => progress easy
  | [ H: ex _ _ |- _ ] => destruct H
  |   H: exists _, _ |- _ => destruct H
  | [ |- context[match ?t with _ => _ end]] =>
      let matched := fresh "matched" in
      destruct t eqn:matched
  | [ H: context[match ?t with _ => _ end] |- _ ] =>
      let matched := fresh "matched" in
      destruct t eqn:matched
  | [ H: context[ifthenelse ?b _ _ _] |- _ ] =>
            let matched := fresh "matched" in
            destruct b eqn:matched
  | [ |- context[ifthenelse ?b _ _ _] ] =>
            let matched := fresh "matched" in
            destruct b eqn:matched
  | |- (S ?T <= ?T)%nat =>
    unify T ignore_termination; apply False_ind; exact unsupported
  | _ => autounfold in *
  end.

Lemma trueProp: forall P, propInBool P = true <-> P.
Proof.
  repeat libStep || unfold propInBool in *.
Qed.

Lemma falseProp: forall P, propInBool P = false <-> (P -> False).
Proof.
  repeat libStep || unfold propInBool in *.
Qed.

Lemma falseNegProp: forall P, negb (propInBool P) = false <-> P.
Proof.
  repeat libStep || unfold propInBool in *.
Qed.

Lemma trueNegProp: forall P, negb (propInBool P) = true <-> (P -> False).
Proof.
  repeat libStep || unfold propInBool in *.
Qed.

Hint Rewrite trueProp falseProp falseNegProp trueNegProp: libR.

Hint Rewrite eqb_true_iff: libR.
Hint Rewrite eqb_false_iff: libR.
Hint Rewrite <- Zeq_is_eq_bool: libR.
Hint Rewrite Z.leb_gt: libR.
Hint Rewrite Z.leb_le: libR.
Hint Rewrite Z.geb_leb: libR.
Hint Rewrite <- Zgt_is_gt_bool: libR.
Hint Rewrite Z.geb_le: libR.

Lemma match_or:
  forall b A e1 e2,
    (exists p: true = b,  e1 p = ifthenelse b A e1 e2) \/
    (exists p: false = b, e2 p = ifthenelse b A e1 e2).
  intros; destruct b; repeat libStep.
Qed.

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

Ltac splitite b B e1 e2 :=
  termNotThere (Mark (b,B,e1,e2) "hello");
  pose proof (Mark (b,B,e1,e2) "hello");
  let HH1 := fresh "H1" in
  let HH2 := fresh "H2" in
  let A1 := fresh "A1" in
  let A2 := fresh "A2" in
  let B1 := fresh "b1" in
  let B2 := fresh "B2" in
  destruct (match_or b B e1 e2) as [ HH1 | HH2 ];
  [
    destruct HH1 as [ A1 B1 ]; (destruct A1 + destruct B1) |
    destruct HH2 as [ A2 B2 ]; (destruct A2 + destruct B2)
  ]
.

Ltac destruct_ifthenelse :=
  match goal with
  | H: context[ifthenelse ?b ?B ?e1 ?e2] |- _ => splitite b B e1 e2
  | |- context[ifthenelse ?b ?B ?e1 ?e2] => splitite b B e1 e2
  end.

Ltac program_simplify :=
  cbn -[Z.add]; intros ; destruct_all_rec_calls ; repeat (destruct_conjs; simpl proj1_sig in * );
  subst*; autoinjections ; try discriminates ;
  try (solve [ red ; intros ; destruct_conjs ; autoinjections ; discriminates ]).

Ltac program_simpl := program_simplify ; try typeclasses eauto with program ; try program_solve_wf.

Ltac destruct_refinement :=
  match goal with
  | |- context[proj1_sig ?T] => destruct T
  | H: context[proj1_sig ?T] |- _ => destruct T
  end.

Ltac t := program_simpl || libStep || destruct_ifthenelse || destruct_refinement.

Obligation Tactic := repeat t.
