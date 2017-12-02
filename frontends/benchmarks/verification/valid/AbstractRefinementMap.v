Require Import Coq.Program.Tactics.
Require Import Coq.Program.Program.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Logic.Classical.
Require Import Omega.

Inductive List (T: Type) :=
| Cons_construct: T -> ((List T) -> (List T))
| Nil_construct: List T.

Program Definition isCons (T: Type) (src: List T) : Prop :=
match src with
| Cons_construct _ _ _ => True
| _ => False
end.

Program Definition isNil (T: Type) (src: List T) : Prop :=
match src with
| Nil_construct _ => True
| _ => False
end.

Program Definition Cons_type (T: Type) : Type :=
{src: List T | isCons T src}.

Program Definition Nil_type (T: Type) : Type :=
{src: List T | isNil T src}.


Ltac step := match goal with 
  | [ H: context[match ?t with _ => _ end] |- _ ] => destruct t
  | [ H: if ?t then _ else _ |- _ ] => destruct t
  | [ |- context[match ?t with _ => _ end] ] => destruct t
  | [ H: ex _ _ |- _ ] => destruct H
  | [ H: isCons _ ?L |- _ ] => is_var L; destruct L
  | _ =>
      congruence || 
      simpl in * || 
      program_simpl || 
      intuition || 
      omega || 
      eauto || 
      discriminate ||
      autounfold in *
  end.

Obligation Tactic := repeat step.

Hint Unfold Cons_type.



Program Definition h (T: Type) (src: Cons_type T) : T :=
match src with
| Cons_construct _ f0 f1 => f0
| _ => let contradiction: False := _ in match contradiction with end
end.

Program Definition t (T: Type) (src: Cons_type T) : List T :=
match src with
| Cons_construct _ f0 f1 => f1
| _ => let contradiction: False := _ in match contradiction with end
end.


Inductive ascii1 (A: Type) (B: Type) :=
| ascii3: (A -> Prop) -> ((A -> B) -> ((B -> Prop) -> (ascii1 A B))).

Program Definition ascii4 (A: Type) (B: Type) (src: ascii1 A B) : Prop :=
match src with
| ascii3 _ _ _ _ _ => True
end.
Hint Unfold ascii4.

Program Definition ascii2 (A: Type) (B: Type) : Type :=
{src: ascii1 A B | ascii4 A B src}.

Program Definition pre (A: Type) (B: Type) (src: ascii2 A B) : A -> Prop :=
match src with
| ascii3 _ _ f0 f1 f2 => f0
end.

Program Definition f (A: Type) (B: Type) (src: ascii2 A B) : A -> B :=
match src with
| ascii3 _ _ f0 f1 f2 => f1
end.

Program Definition ens (A: Type) (B: Type) (src: ascii2 A B) : B -> Prop :=
match src with
| ascii3 _ _ f0 f1 f2 => f2
end.


Definition content (T: Type) (thiss: List T) : set (T). Admitted.
Program Fixpoint contains (T: Type) (thiss: List T) (v: T): Prop :=
match thiss with
| Cons_construct _ h t => h = v \/ contains T t v
| Nil_construct _ => False
end.

Program Definition inv (A: Type) (B: Type) (thiss: ascii1 A B) : Prop :=
  forall x: A, ((pre A B thiss) x) -> ((ens A B thiss) ((f A B thiss) x)).

Program Definition ascii5 A B := { f: ascii2 A B | inv A B f }.

Hint Unfold inv.
Hint Unfold ascii5.

Program Definition apply (A: Type) (B: Type) (thiss: ascii5 A B) (x: A) (stainlessPrecondition: (pre A B thiss) x) : {res: B | (ens A B thiss) res} :=
(f A B thiss) x.

Program Fixpoint map (A: Type) (B: Type) (l: List A) (f: ascii5 A B) 
  (stainlessPrecondition: forall x: A, contains A l x -> ((pre A B f) x)): 
  { res: List B | 
    forall x: B, contains B res x -> (ens A B f) x
  } :=
match l with
| Cons_construct _ y ys => Cons_construct B (apply A B f y _) (map A B ys f _)
| Nil_construct _ => Nil_construct B
end.
