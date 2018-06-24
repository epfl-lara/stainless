Require Import ZArith.
Require Import Equations.Equations.

Set Program Mode.

Inductive List (T: Type) :=
| Cons_construct: T -> ((List T) -> (List T))
| Nil_construct: List T.

Definition isCons (T: Type) (src: List T) : bool :=
match src with
| Cons_construct _ _ _ => true
| _ => false
end.

Definition isNil (T: Type) (src: List T) : bool :=
match src with
| Nil_construct _ => true
| _ => false
end.

Definition Cons_type (T: Type) : Type := {src: List T |  True }.

Definition head (T: Type) (src: Cons_type T) : T :=
match src with
| Cons_construct _ f0 f1 => f0
| _ => let contradiction: False := _ in match contradiction with end
end.

Admit Obligations.

Definition tail (T: Type) (src: Cons_type T) : List T :=
match src with
| Cons_construct _ f0 f1 => f1
| _ => let contradiction: False := _ in match contradiction with end
end.

Admit Obligations.

Definition size (T: Type) (l: List T): { res : Z | True }. Admitted.

Definition ifthenelse b A (e1: true = b -> A) (e2: false = b -> A): A :=
  match b as B return (B = b -> A) with
  | true => fun H => e1 H
  | false => fun H => e2 H
  end eq_refl.

Parameter ignore_termination: nat.

Definition filter_rt1_type (T: Type) (l: List T) (p: T -> bool) : Type :=
{res: List T |
   ifthenelse
	(ifthenelse (Z.leb (proj1_sig (size T res)) 0) bool
		(fun _ => false )
		(fun _ => false ))
	bool
	(fun _ => false )
	(fun _ => false ) = true }.

Fail Next Obligation.

Hint Unfold filter_rt1_type.

Equations (noind) filter (T: Type) (l: List T) (p: T -> bool) : filter_rt1_type T l p := 
  filter T l p by rec ignore_termination lt :=
  filter T l p :=
    ifthenelse (isNil _ l) (List T)
      (fun _ => Nil_construct T )
      (fun _ => ifthenelse
              (ifthenelse true bool
                      (fun _ => p (head T l) )
                      (fun _ => false ))
              (List T)
              (fun _ => Cons_construct T (head T l) (proj1_sig (filter T (tail T l) p)) )
                      (fun _ => proj1_sig (filter T (tail T l) p) ))
 .

Admit Obligations.

Goal
  forall T (p: T -> bool) (h: T) (l: List T) (matched: p h = true)
      (H:
         filter T (Nil_construct T) p =
         exist
           _
           (
             ifthenelse (p h) (List T)
               (fun _ => Cons_construct T h (`(filter T l p)))
               (fun _ =>  `(filter T l p))
           )
           (
             filter_obligation_7 T (Cons_construct T h l) p
            (fun (T : Type) (l : List T) (p : T -> bool) (_ : (ignore_termination <
                                                                   ignore_termination)%nat) => 
             filter T l p))),
    False.
Proof.
  intros.
  rewrite matched in H.
