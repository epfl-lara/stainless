Require Import SLC.Lib.
Require Import SLC.Booleans.
Require Import Coq.Logic.Classical.

Axiom classicT: forall P: Prop, P + ~P.

Definition propInBool (P: Prop): bool :=
 if (classicT P)
 then true
 else false.

Notation "'B@(' p ')'" := (propInBool p) (at level 80).


(* Hint Unfold propInBool. *)

Lemma Aeq_dec_all: forall T: Type, forall x y: T, {x = y} + {x <> y}.
  intros.
  pose proof classicT (x  = y) as H.
  destruct H; intuition.
Qed.


Lemma trueProp: forall P, propInBool P = true <-> P.
Proof.
  repeat libStep || unfold propInBool in * || ifthenelse_step.
Qed.

Lemma falseProp: forall P, propInBool P = false <-> (P -> False).
Proof.
  repeat libStep || unfold propInBool in * || ifthenelse_step.
Qed.

Lemma falseNegProp: forall P, negb (propInBool P) = false <-> P.
Proof.
  repeat libStep || unfold propInBool in * || ifthenelse_step.
Qed.

Lemma trueNegProp: forall P, negb (propInBool P) = true <-> (P -> False).
Proof.
  repeat libStep || unfold propInBool in * || ifthenelse_step.
Qed.

Lemma trueProp2: forall P, true = propInBool P <-> P.
Proof.
  repeat libStep || unfold propInBool in * || ifthenelse_step.
Qed.

Lemma falseProp2: forall P, false = propInBool P <-> (P -> False).
Proof.
  repeat libStep || unfold propInBool in * || ifthenelse_step.
Qed.

Lemma falseNegProp2: forall P, false = negb (propInBool P) <-> P.
Proof.
  repeat libStep || unfold propInBool in *  || ifthenelse_step.
Qed.

Lemma trueNegProp2: forall P, true = negb (propInBool P) <-> (P -> False).
Proof.
  repeat libStep || unfold propInBool in * || ifthenelse_step.
Qed.


Lemma equivProps: forall P1 P2,
    propInBool P1 = propInBool P2 <->
    (P1 <-> P2).
Proof.
  repeat libStep || unfold propInBool in * || ifthenelse_step.
Qed.

Hint Rewrite trueProp falseProp falseNegProp trueNegProp equivProps: libProp.
Hint Rewrite trueProp2 falseProp2 falseNegProp2 trueNegProp2: libProp.

Lemma implication:
  forall A B: Prop,
    (A \/ (B -> False)) <-> (B -> A).
Proof.
  intros A B; pose proof (classicT B); repeat libStep.
Qed.

Lemma implication2:
  forall A B: Prop,
    ((A -> False) \/ B) <-> (A -> B).
Proof.
  intros A B; pose proof (classicT A); repeat libStep.
Qed.

Hint Rewrite implication: libProp.
Hint Rewrite implication2: libProp.

Ltac has_prop_in_bool E :=
  match E with
  | context[propInBool] => idtac
  end.

Ltac t_propbool :=
  match goal with
  | H: ?E = ?b |- _ =>
    let pib := fresh "pib" in
    has_prop_in_bool E;
    not_literal b;  
    destruct b eqn:pib
  | H: ?b = ?E |- _ =>
    let pib := fresh "pib" in
    has_prop_in_bool E;
    not_literal b;
    destruct b eqn:pib
  end.

Lemma if_then_false:
  forall b (e1: b = true -> bool),
           ifthenelse b bool e1 (fun _ => false) =
           propInBool (exists H: b = true, e1 H = true).
Proof.
  repeat libStep || ifthenelse_step || exists eq_refl || t_bool || autorewrite with libProp in *.                                       
  rewrite (Eqdep_dec.UIP_refl_bool true exH) in *; auto.
Qed.

Lemma if_then_true:
  forall b (e1: b = true -> bool),
           ifthenelse b bool e1 (fun _ => true) = 
           negb b || propInBool (exists H: b = true, e1 H = true).
Proof.
  repeat libStep || ifthenelse_step || exists eq_refl || t_bool || autorewrite with libProp in *.
  rewrite (Eqdep_dec.UIP_refl_bool true exH) in *; repeat libStep.
Qed.

Lemma if_false_else:
  forall b (e2: b = false -> bool),
           ifthenelse b bool (fun _ => false) e2 =
           propInBool (exists H: b = false, e2 H = true).
Proof.
  repeat libStep || ifthenelse_step || exists eq_refl || t_bool || autorewrite with libProp in *.
  rewrite (Eqdep_dec.UIP_refl_bool false exH) in *; auto.
Qed.

Lemma if_true_else:
  forall b (e2: b = false -> bool),
           ifthenelse b bool (fun _ => true) e2 = 
           b || propInBool (exists H: b = false, e2 H = true).
Proof.
  repeat libStep || ifthenelse_step || exists eq_refl || t_bool || autorewrite with libProp in *.
  rewrite (Eqdep_dec.UIP_refl_bool false exH) in *; repeat libStep.
Qed.

Hint Rewrite if_true_else if_false_else if_then_true if_then_false: libBoolExists.

Lemma obvious_exist:
  forall (P1 P2: Prop), (exists _ : P1, P2) <-> (P1 /\ P2).
Proof.
  repeat libStep; eauto.
Qed.

Hint Rewrite obvious_exist: libProp.
