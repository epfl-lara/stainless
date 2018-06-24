Require Equations.Equations.

Set Program Mode.

Definition ifthenelse b A (e1: true = b -> A) (e2: false = b -> A): A. Admitted.
  
Definition List (T: Type): Type. Admitted.
Definition isCons (T: Type) (src: List T): bool. Admitted.
Definition Cons_type (T: Type): Type := {src: List T | (isCons T src = true)}.
Definition head (T: Type) (src: Cons_type T): T. Admitted.
Definition tail (T: Type) (src: Cons_type T): List T. Admitted.
Definition f_type (T R: Type) (l: List T): Type := R -> (T -> R).
Definition foldLeft_type (T R: Type) (l: List T): Type := R.

Equations foldLeft (T R: Type) (l: List T) (z: R) (f: f_type T R l): foldLeft_type T R l := 
foldLeft T R l z f by rec 0 lt :=
foldLeft T R l z f :=
  ifthenelse (isCons _ l) R
             (fun _ => foldLeft T R (tail T l) (f z (head T l)) f)
             (fun _ => z).

Admit Obligations.