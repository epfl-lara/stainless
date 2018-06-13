Definition Rewrite T t1 t2 := @eq T t1 t2.

Lemma rewrite_to_equal: forall T (t1 t2: T), Rewrite T t1 t2 -> t1 = t2.
Proof.
  unfold Rewrite; auto.
Qed.

Lemma equal_to_rewrite: forall T (t1 t2: T), t1 = t2 -> Rewrite T t1 t2.
Proof.
  unfold Rewrite; auto.
Qed.
  
Ltac add_equation E := pose proof (equal_to_rewrite _ _ _ E).

Ltac isNotMatch  M :=
  match M with
  | match _ with _ => _ end => fail 1
  | match _ with _ => _ end _ => fail 1
  | _ => idtac
  end.

Ltac rewrite_unfoldings :=
  repeat match goal with
         | H: Rewrite ?T ?t1 ?t2 |- _ =>
           isNotMatch t2;
           rewrite (rewrite_to_equal _ _ _ H) in *
(*           let r := constr:(rewrite_to_equal _ _ _ H) in
               revert H;
               (rewrite r in * |-; intros H; try rewrite r) ||
               (intros H; rewrite r)*)
         end.
