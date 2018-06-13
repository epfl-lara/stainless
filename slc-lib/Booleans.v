Require Import SLC.Lib.

Require Import ZArith.
Require Import Coq.Bool.Bool.

Hint Rewrite eqb_true_iff: libBool.
Hint Rewrite eqb_false_iff: libBool.
Hint Rewrite orb_true_iff: libBool.
Hint Rewrite orb_false_iff: libBool.

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

Ltac ifthenelse_step := match goal with
  | [ |- context[match ?t with _ => _ end]] =>
      let matched := fresh "matched" in
      destruct t eqn:matched
  | [ H: context[match ?t with _ => _ end] |- _ ] =>
      let matched := fresh "matched" in
      destruct t eqn:matched
  | [ |- context[ifthenelse ?b _ _ _] ] =>
      let matched := fresh "matched" in
      destruct b eqn:matched
  | [ H: context[ifthenelse ?b _ _ _] |- _ ] =>
      let matched := fresh "matched" in
      destruct b eqn:matched
end.


Lemma ifthenelse_rewrite_2: forall T b e1 e2 value,
    ifthenelse b T e1 e2 = value <->
    (
      (exists H1: true = b, e1 H1 = value) \/
      (exists H2: false = b, e2 H2 = value)
    ).
Proof.
  repeat libStep || ifthenelse_step; eauto.
Qed.

Lemma ifthenelse_rewrite_2': forall T b e1 e2 value,
    value = ifthenelse b T e1 e2 <->
    (
      (exists H1: true = b, e1 H1 = value) \/
      (exists H2: false = b, e2 H2 = value)
    ).
Proof.
  repeat libStep || ifthenelse_step; eauto.
Qed.

Lemma ifthenelse_rewrite_3: forall T b e1 e2 value,
    (forall H1: true = b, e1 H1 = value) ->
    (forall H2: false = b, e2 H2 = value) ->
    ifthenelse b T e1 e2 = value.
Proof.
  repeat libStep || ifthenelse_step.
Qed.

Lemma ifthenelse_rewrite_4: forall T (b: bool) (e1 e2 value: T),
  (if b then e1 else e2) = value -> 
    ((b = true /\ e1 = value) \/ (b = false /\ e2 = value)).
Proof.
  repeat libStep || ifthenelse_step.
Qed.

Lemma ifthenelse_rewrite_4': forall T (b: bool) (e1 e2 value: T),
  value = (if b then e1 else e2) -> 
    ((b = true /\ e1 = value) \/ (b = false /\ e2 = value)).
Proof.
  repeat libStep || ifthenelse_step.
Qed.

Hint Rewrite ifthenelse_rewrite_2: libCase.
Hint Rewrite ifthenelse_rewrite_2': libCase.
Hint Rewrite ifthenelse_rewrite_4: libCase.
Hint Rewrite ifthenelse_rewrite_4': libCase.


Ltac rewrite_ifthenelse :=
  match goal with
  | [ |- (ifthenelse _ _ _ _) = _ ] => apply ifthenelse_rewrite_3
  | [ |- _ = (ifthenelse _ _ _ _) ] => apply eq_sym; apply ifthenelse_rewrite_3
(*  | [ H: (if ?b then ?e1 else ?e2) = ?value |- _ ] => poseNew(Mark H "if_then_else_rewrite"); pose proof(ifthenelse_rewrite_4 _ _ _ _ H)
  | [ H: ?value = if ?b then ?e1 else ?e2 |- _ ] => poseNew(Mark H "if_then_else_rewrite"); pose proof(ifthenelse_rewrite_4 _ _ _ _ (eq_sym H)) *)
  end.


Lemma match_or:
  forall b A e1 e2,
    (exists p: true = b,  e1 p = ifthenelse b A e1 e2) \/
    (exists p: false = b, e2 p = ifthenelse b A e1 e2).
  intros; destruct b; repeat libStep; eauto.
Qed.

Ltac splitite b B e1 e2 :=
  let S := fresh "S" in
  let HH1 := fresh "HH" in
  let HH2 := fresh "HH" in
  let M1 := fresh "MM" in 
  let M2 := fresh "MM" in 
  let X := fresh "XX" in
  let Y := fresh "YY" in
  let B1 := fresh "BB" in
  let B2 := fresh "BB" in
  let cpX := fresh "cpX" in
  let cpY := fresh "cpY" in
  let MM := fresh "Mark" in
  poseNamed MM (Mark b "splitting if then else");
  pose proof (Mark MM "splitting if then else");
  destruct (match_or b B e1 e2) as [ HH1 | HH2 ];
  [
    destruct HH1 as [ X B1 ];
    try rewrite <- X in *;
    try rewrite <- B1 in *;
    clear B1;
    pose proof (Mark X "not_usable") as M1;
    pose proof X as cpX
      |
    destruct HH2 as [ Y B2 ];
    try rewrite <- Y in *;
    try rewrite <- B2 in *;
    clear B2;
    pose proof (Mark Y "not_usable") as M2;
    pose proof Y as cpY 
  ]
.

Ltac destruct_ifthenelse :=
  match goal with
  | H: context[ifthenelse ?b ?B ?e1 ?e2] |- _ => usable H; splitite b B e1 e2
  | |- context[ifthenelse ?b ?B ?e1 ?e2] => splitite b B e1 e2
  end.

Lemma if_then_false:
  forall b (e1: true = b -> bool),
           ifthenelse b bool e1 (fun _ => false) = true <->
           exists H: true = b, e1 H = true.
Proof.
  repeat libStep || ifthenelse_step || exists eq_refl.
Qed.

Lemma if_then_false2:
  forall b e1,
           (ifthenelse b bool (fun _ => e1) (fun _ => false)) = true <->
           b = true /\ e1 = true.
Proof.
  repeat libStep || ifthenelse_step.
Qed.


Lemma if_then_true:
  forall b (e1: true = b -> bool),
           ifthenelse b bool e1 (fun _ => true) = false <->
           exists H: true = b, e1 H = false.
Proof.
  repeat libStep || ifthenelse_step || exists eq_refl.
Qed.

Lemma if_then_true2:
  forall b e1,
           (ifthenelse b bool (fun _ => e1) (fun _ => true)) = false <->
           b = true /\ e1 = false.
Proof.
  repeat libStep || ifthenelse_step.
Qed.

Lemma if_false_else:
  forall b (e2: false = b -> bool),
           ifthenelse b bool (fun _ => false) e2 = true <->
           exists H: false = b, e2 H = true.
Proof.
  repeat libStep || ifthenelse_step || exists eq_refl.
Qed.

Lemma if_false_else2:
  forall b e2,
           (ifthenelse b bool (fun _ => false) (fun _ => e2)) = true <->
           b = false /\ e2 = true.
Proof.
  repeat libStep || ifthenelse_step.
Qed.

Lemma if_true_else:
  forall b (e2: false = b -> bool),
           ifthenelse b bool (fun _ => true) e2 = false <->
           exists H: false = b, e2 H = false.
Proof.
  repeat libStep || ifthenelse_step || exists eq_refl.
Qed.

Lemma if_true_else2:
  forall b e2,
           (ifthenelse b bool (fun _ => true) (fun _ => e2)) = false <->
           b = false /\ e2 = false.
Proof.
  repeat libStep || ifthenelse_step.
Qed.

Hint Rewrite if_true_else if_false_else if_then_true if_then_false: libBoolExists.
Hint Rewrite if_true_else2 if_false_else2 if_then_false2 if_then_true2: libBool.

Lemma negb_equal:
  forall b1 b2,
    negb b1 = negb b2 <-> b1 = b2.
Proof.
  destruct b1; destruct b2; repeat libStep.
Qed.

Hint Rewrite negb_equal: libBool.

Ltac t_bool_simpl :=
  match goal with
  | H: ?b = ?l |- _ => 
    usable H; not_literal b; literal l; rewrite H in *
  end.

Ltac t_bool :=
  match goal with
  | _ => apply eq_true_not_negb
  | |- ?b1 = ?b2 => not_literal b1; not_literal b2; apply eq_iff_eq_true
  | _ => t_bool_simpl
  end.



Lemma if_then_false0:
  forall b: bool, forall e1,
           (if b then e1 else false) = true <->
           b = true /\ e1 = true.
Proof.
  repeat libStep || ifthenelse_step.
Qed.


Lemma if_then_true0:
  forall b: bool, forall e1,
           (if b then e1 else true) = false <->
           b = true /\ e1 = false.
Proof.
  repeat libStep || ifthenelse_step.
Qed.

Lemma if_false_else0:
  forall b: bool, forall e2,
           (if b then false else e2) = true <->
           b = false /\ e2 = true.
Proof.
  repeat libStep || ifthenelse_step.
Qed.


Lemma if_true_else0:
  forall b: bool, forall e2,
           (if b then true else e2) = false <->
           b = false /\ e2 = false.
Proof.
  repeat libStep || ifthenelse_step.
Qed.

Hint Rewrite if_then_true0 : libBool.
Hint Rewrite if_then_false0 : libBool.
Hint Rewrite if_true_else0 : libBool.
Hint Rewrite if_false_else0 : libBool.

(**
Lemma rewrite_and_true:
  forall b: bool, b &&b true = b.
Proof.
  repeat libStep || ifthenelse_step.
Qed.

Lemma rewrite_and_true2:
  forall a b: bool, b &&b true = a -> b = a.
Proof.
  repeat libStep || ifthenelse_step.
Qed.

Lemma rewrite_true_and:
  forall b: bool, true &&b b = b.
Proof.
  repeat libStep.
Qed.

Lemma rewrite_and_false:
  forall b: bool, b &&b false = false.
Proof.
  repeat libStep || ifthenelse_step.
Qed.

Lemma rewrite_false_and:
  forall b: bool, false &&b b = false.
Proof.
  repeat libStep.
Qed. 

Hint Rewrite rewrite_and_true: libBool.
Hint Rewrite rewrite_true_and: libBool.
Hint Rewrite rewrite_and_false: libBool.
Hint Rewrite rewrite_false_and: libBool.**)
