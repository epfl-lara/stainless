Require Import SLC.Lib.

Require Import ZArith.
Require Import Coq.Bool.Bool.

Hint Rewrite eqb_true_iff: libR.
Hint Rewrite eqb_false_iff: libR.
Hint Rewrite <- Zeq_is_eq_bool: libR.
Hint Rewrite orb_true_iff: libR.

(*
Definition bool_and b1 (b2: true = b1 -> bool): bool :=
  match b1 as B return (B = b1 -> bool) with
  | true => b2
  | false => fun _ => false
  end eq_refl.

Notation "b1 &b b2" := (bool_and b1 (fun _ => b2)) (at level 80, right associativity).

Lemma bool_and_iff: forall b1 b2,
    (b1 &b b2) = true <-> b1 = true /\ b2 = true.
  unfold bool_and; repeat libStep.
Qed.

Hint Rewrite bool_and_iff: libR.
 *)

Notation "b1 &&b b2" := (if b1 then b2 else false) (at level 50). 


Definition ifthenelse b A (e1: true = b -> A) (e2: false = b -> A): A :=
  match b as B return (B = b -> A) with
  | true => fun H => e1 H
  | false => fun H => e2 H
  end eq_refl.

Notation "'ifb' '(' b ')' '{' T '}' 'then' '{' p1 '}' e1 'else' '{' p2 '}' e2" :=
  (ifthenelse b T (fun p1 => e1) (fun p2 => e2)) (at level 80).
Notation "'ifb' '(' b ')' '{' T '}' 'then' e1 'else' e2" :=
  (ifthenelse b T (fun _ => e1) (fun _ => e2)) (at level 80).

Lemma match_or:
  forall b A e1 e2,
    (exists p: true = b,  e1 p = ifthenelse b A e1 e2) \/
    (exists p: false = b, e2 p = ifthenelse b A e1 e2).
  intros; destruct b; repeat libStep; eauto.
Qed.

Ltac ifthenelse_step := match goal with
  | [ H: context[ifthenelse ?b _ _ _] |- _ ] =>
            let matched := fresh "matched" in
            destruct b eqn:matched
  | [ |- context[ifthenelse ?b _ _ _] ] =>
            let matched := fresh "matched" in
            destruct b eqn:matched
end.

Lemma ifthenelse_rewrite_3: forall T b e1 e2 value,
    (forall H1: true = b, e1 H1 = value) ->
    (forall H2: false = b, e2 H2 = value) ->
    ifthenelse b T e1 e2 = value.
Proof.
  repeat libStep || ifthenelse_step.
Qed.

Lemma ifthenelse_rewrite_4: forall {T} (b: bool) (e1 e2 value: T),
  (if b then e1 else e2) = value -> 
    ((b = true /\ e1 = value) \/ (b = false /\ e2 = value)).
Proof.
  repeat libStep.
Qed.

Ltac splitite b B e1 e2 :=
  poseNew (Mark (b,B,e1,e2) "splitting if then else");
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

Ltac rewrite_ifthenelse :=
  match goal with
  | [ |- (ifthenelse _ _ _ _) = _ ] => apply ifthenelse_rewrite_3
  | [ |- _ = (ifthenelse _ _ _ _) ] => apply eq_sym; apply ifthenelse_rewrite_3
  | [ H: (if ?b then ?e1 else ?e2) = ?value |- _ ] => poseNew(Mark H "if_then_else_rewrite"); pose proof(ifthenelse_rewrite_4 _ _ _ _ H)
  | [ H: ?value = if ?b then ?e1 else ?e2 |- _ ] => poseNew(Mark H "if_then_else_rewrite"); pose proof(ifthenelse_rewrite_4 _ _ _ _ (eq_sym H))
  end.

Lemma rewrite_and_true:
  forall b: bool, b &&b true = b.
Proof.
  repeat libStep.
Qed.

Lemma rewrite_and_true2:
  forall a b: bool, b &&b true = a -> b = a.
Proof.
  repeat libStep.
Qed.

Lemma rewrite_true_and:
  forall b: bool, true &&b b = b.
Proof.
  repeat libStep.
Qed.

Lemma rewrite_and_false:
  forall b: bool, b &&b false = false.
Proof.
  repeat libStep.
Qed.

Lemma rewrite_false_and:
  forall b: bool, false &&b b = false.
Proof.
  repeat libStep.
Qed.

Hint Rewrite rewrite_and_true: libR.
Hint Rewrite rewrite_true_and: libR.
Hint Rewrite rewrite_and_false: libR.
Hint Rewrite rewrite_false_and: libR.

Lemma if_then_false:
  forall b (e1: true = b -> bool),
           ifthenelse b bool e1 (fun _ => false) = true ->
           b = true /\ exists H: true = b, e1 H = true.
Proof.
  repeat libStep || ifthenelse_step || exists eq_refl.
Qed.

Lemma if_then_false2:
  forall b e1,
           (ifthenelse b bool (fun _ => e1) (fun _ => false)) = true ->
           b = true /\ e1 = true.
Proof.
  repeat libStep || ifthenelse_step.
Qed.

Ltac literal b :=
  (unify b true) + (unify b false).

Ltac not_literal b := tryif literal b then fail else idtac.

Ltac t_bool :=
  match goal with
  | H: ?b &&b true = ?a |- _ =>
    let H2 := fresh H in
    poseNew (Mark (a,b) "rewrite_and_true");
    pose proof (rewrite_and_true2 _ _ H) as H2                            
  | H: eqb ?a ?b = true |- _ =>
    let H2 := fresh H in
    poseNew (Mark H "eqb_true_iff");
    pose proof (proj1 (eqb_true_iff _ _) H) as H2                             
  | H: ifthenelse ?b bool ?a _ = true |- _ =>
    let H2 := fresh H in
    poseNew (Mark (a,b) "if_then_false2");
    pose proof (if_then_false2 _ _ H) as H2                              
  | H: true = ifthenelse ?b bool ?a _ |- _ =>
    let H2 := fresh H in
    poseNew (Mark (a,b) "if_then_false2");
    pose proof (if_then_false2 _ _ (eq_sym H)) as H2                          
  | H: ifthenelse ?b bool ?a _ = true |- _ =>
    let H2 := fresh H in
    poseNew (Mark (a,b) "if_then_false");
    pose proof (if_then_false _ _ H) as H2                              
  | H: true = ifthenelse ?b bool ?a _ |- _ =>
    let H2 := fresh H in
    poseNew (Mark (a,b) "if_then_false");
    pose proof (if_then_false2 _ _ (eq_sym H)) as H2    
  | H: ?b <> true |- _ => 
    let H2 := fresh H in
    poseNew (Mark (b) "eq_true_not_negb");
    pose proof (eq_true_not_negb _ H) as H2
  | H: true <> ?b |- _ => 
    let H2 := fresh H in
    poseNew (Mark (b) "eq_true_not_negb");
    pose proof (eq_true_not_negb _ (not_eq_sym H)) as H2
  | |- ?b1 = ?b2 => not_literal b1; not_literal b2; apply eq_iff_eq_true
  end.