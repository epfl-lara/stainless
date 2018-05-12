Require Import SLC.Lib.

Require Import ZArith.
Require Import Coq.Bool.Bool.

Hint Rewrite eqb_true_iff: libR.
Hint Rewrite eqb_false_iff: libR.
Hint Rewrite <- Zeq_is_eq_bool: libR.
Hint Rewrite orb_true_iff: libR.
Hint Rewrite orb_false_iff: libR.

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

Ltac ifthenelse_step := match goal with
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

Hint Rewrite ifthenelse_rewrite_2: libR.
Hint Rewrite ifthenelse_rewrite_2': libR.
Hint Rewrite ifthenelse_rewrite_4: libR.
Hint Rewrite ifthenelse_rewrite_4': libR.

Lemma match_or:
  forall b A e1 e2,
    (exists p: true = b,  e1 p = ifthenelse b A e1 e2) \/
    (exists p: false = b, e2 p = ifthenelse b A e1 e2).
  intros; destruct b; repeat libStep; eauto.
Qed.

Ltac splitite b B e1 e2 :=
  let S := fresh "S" in
  let HH1 := fresh "H1" in
  let HH2 := fresh "H2" in
  let M1 := fresh "M1" in 
  let M2 := fresh "M2" in 
  let A1 := fresh "A1" in
  let A2 := fresh "A2" in
  let B1 := fresh "B1" in
  let B2 := fresh "B2" in
  let cpA1 := fresh "cpA1" in
  let cpA2 := fresh "cpA2" in
  poseNew (Mark (b,B,e1,e2) "splitting if then else");
  destruct (match_or b B e1 e2) as [ HH1 | HH2 ];
  [
    destruct HH1 as [ A1 B1 ];
    try rewrite <- A1 in *;
    try rewrite <- B1 in *;
    clear B1;
    pose proof (Mark A1 "not_usable") as M1;
    pose proof A1 as cpA1 
      |
    destruct HH2 as [ A2 B2 ];
    try rewrite <- A2 in *;
    try rewrite <- B2 in *;
    clear B2;
    pose proof (Mark A2 "not_usable") as M2;
    pose proof A2 as cpA2 
  ]
.

Ltac destruct_ifthenelse :=
  match goal with
  | H: context[ifthenelse ?b ?B ?e1 ?e2] |- _ => usable H; splitite b B e1 e2
  | |- context[ifthenelse ?b ?B ?e1 ?e2] => splitite b B e1 e2
  end.

Ltac rewrite_ifthenelse :=
  match goal with
  | [ |- (ifthenelse _ _ _ _) = _ ] => apply ifthenelse_rewrite_3
  | [ |- _ = (ifthenelse _ _ _ _) ] => apply eq_sym; apply ifthenelse_rewrite_3
(*  | [ H: (if ?b then ?e1 else ?e2) = ?value |- _ ] => poseNew(Mark H "if_then_else_rewrite"); pose proof(ifthenelse_rewrite_4 _ _ _ _ H)
  | [ H: ?value = if ?b then ?e1 else ?e2 |- _ ] => poseNew(Mark H "if_then_else_rewrite"); pose proof(ifthenelse_rewrite_4 _ _ _ _ (eq_sym H)) *)
  end.

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

Hint Rewrite rewrite_and_true: libR.
Hint Rewrite rewrite_true_and: libR.
Hint Rewrite rewrite_and_false: libR.
Hint Rewrite rewrite_false_and: libR.

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

Hint Rewrite if_then_false if_then_false2 if_then_true if_then_true2: libR.
Hint Rewrite if_true_else if_true_else2 if_false_else if_false_else2 :libR.

Lemma negb_equal:
  forall b1 b2,
    negb b1 = negb b2 <-> b1 = b2.
Proof.
  destruct b1; destruct b2; repeat libStep.
Qed.

Hint Rewrite negb_equal: libR.

Ltac literal b :=
  (unify b true) + (unify b false).

Ltac not_literal b := tryif literal b then fail else idtac.

Ltac t_bool_simpl :=
  match goal with
  | H: ?b = ?l |- _ => 
    usable H; not_literal b; literal l; rewrite H in *
  | H: ?l = ?b |- _ => 
    usable H; not_literal b; literal l; rewrite <- H in *    
  end.

Ltac t_bool :=
  match goal with
  | _ => apply eq_true_not_negb
  | |- ?b1 = ?b2 => not_literal b1; not_literal b2; apply eq_iff_eq_true
  | _ => t_bool_simpl
  end.


(* Not done yet 
Ltac t_bool_simpl := 
  match goal with
  | H: negb ?b = true |- _ =>
    let H2 := fresh "H" in
    poseNew(Mark H "not_bool_eq_true");
    pose proof (negb_true_iff _ H) as H2;
    rewrite H2 in *
  | H: negb ?b = false |- _ =>
    poseNew(Mark H "not_bool_eq_false");
    pose proof (negb_false_iff _ H) as H2;
    rewrite H2 in *
  | H: true = negb ?b |- _ =>
    poseNew(Mark H "true_eq_not_bool");
    pose proof (negb_true_iff _ (eq_sym H)) as H2;
    rewrite H2 in *
  | H: false = negb ?b |- _ =>
    poseNew(Mark H "false_eq_not_bool");
    pose proof (negb_false_iff _ (eq_sym H)) as H2

  | H: ?b = true |- _ =>
    poseNew(Mark (H) "bool_eq_true");
    rewrite H in *;
    clear H
  | H: ?b = false |- _ =>
    poseNew(Mark (H) "bool_eq_false");
    rewrite H in *;
    clear H
  | H: true = ?b |- _ =>
    poseNew(Mark (H) "true_eq_bool");
    rewrite H in *
  | H: false = ?b |- _ =>
    poseNew(Mark (H) "false_eq_bool");
    pose proof (eq_sym H)


  end.
*)


  (*| H: ?b &&b true = ?a |- _ =>
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
    poseNew (Mark (b) "not_true_is_false");
    pose proof (not_true_is_false _ H) as H2
  | H: true <> ?b |- _ => 
    let H2 := fresh H in
    poseNew (Mark (b) "not_true_is_false");
    pose proof (not_true_is_false _ (not_eq_sym H)) as H2
  | H: ?b <> false |- _ => 
    let H2 := fresh H in
    poseNew (Mark (b) "not_false_is_true");
    pose proof (not_false_is_true _ H) as H2
  | H: false <> ?b |- _ => 
    let H2 := fresh H in
    poseNew (Mark (b) "not_false_is_true");
    pose proof (not_false_is_true _ (not_eq_sym H)) as H2
  *)
