Require Import SLC.Lib.
Require Import SLC.Booleans.

Definition Rewrite T t1 t2 := @eq T t1 t2.

Lemma rewrite_to_equal: forall T (t1 t2: T), Rewrite T t1 t2 -> t1 = t2.
Proof.
  unfold Rewrite; auto.
Qed.

Lemma equal_to_rewrite: forall T (t1 t2: T), t1 = t2 -> Rewrite T t1 t2.
Proof.
  unfold Rewrite; auto.
Qed.

Lemma swap_rewrite: forall T t1 t2, Rewrite T t1 t2 -> Rewrite T t2 t1.
Proof.
  unfold Rewrite; auto.
Qed.

Ltac add_equation E :=
  let U := fresh "U" in
  pose proof (equal_to_rewrite _ _ _ E) as U.

Ltac unknown b :=
  match goal with
  | H: b = true |- _ => fail 1
  | H: b = false |- _ => fail 1
  | _ => idtac
  end.

Ltac not_rewritable  M :=
  match M with
  | match _ with _ => _ end => idtac
  | match _ with _ => _ end _ => idtac
  | ifthenelse ?b _ _ _ => unknown b; idtac
  | exist _ ?N _ => not_rewritable N
  end.

Ltac writable M := tryif not_rewritable M then fail else idtac.

Ltac is_application  M :=
  match M with
  | ?M1 ?M2 => idtac
  end.

Ltac not_application M := tryif is_application M then fail else idtac.

Ltac rewrite_unfoldings :=
  repeat match goal with
         | H: Rewrite ?T ?t1 ?t2 |- _ =>
           is_application t1;
           writable t2;
           rewrite H in *
(*           let r := constr:(rewrite_to_equal _ _ _ H) in
               revert H;
               (rewrite r in * |-; intros H; try rewrite r) ||
               (intros H; rewrite r)*)
         end.

Ltac rewrite_equations :=
  match goal with
  | U: Rewrite ?T ?t1 ?t2 |- _ => is_application t2; not_application t1; unfold Rewrite in U
  | U: true = ?b |- _ => not_literal b; apply eq_sym in U
  | U: false = ?b |- _ => not_literal b; apply eq_sym in U
  | U: _ = exist _ _ _ |- _ => rewrite U in *
  | U: exist _ _ _ = _ |- _ => rewrite <- U in *
  end.


Ltac clearUnusedRewrites :=
    repeat match goal with
           | H: Rewrite _ _ ?t2 |- _ => not_rewritable t2; clear H
           end.
   
Ltac clearRewrites :=
    repeat match goal with
           | H: Rewrite _ _ ?t2 |- _ => clear H
           end.
   
