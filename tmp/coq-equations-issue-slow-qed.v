Require Import Equations.Equations.

Require Import ZArith.

Open Scope Z_scope.

Set Program Mode.


Fail Next Obligation.

Inductive List (T: Type) :=
| Cons_construct: T -> ((List T) -> (List T))
| Nil_construct: List T.

Definition isCons (T: Type) (src: List T) : bool :=
match src with
| Cons_construct _ _ _ => true
| _ => false
end.

Admit Obligations.

Hint Unfold  isCons: recognizers. 

Definition isNil (T: Type) (src: List T) : bool :=
match src with
| Nil_construct _ => true
| _ => false
end.

Admit Obligations.

Hint Unfold  isNil: recognizers. 

  
Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Definition h (T: Type) (src: Cons_type T) : T :=
match src with
| Cons_construct _ f0 f1 => f0
| _ => let contradiction: False := _ in match contradiction with end
end.

Admit Obligations.

Definition t4 (T: Type) (src: Cons_type T) : List T :=
match src with
| Cons_construct _ f0 f1 => f1
| _ => let contradiction: False := _ in match contradiction with end
end.

Admit Obligations.


Definition set (t: Type): Type. Admitted.
Definition set_empty {T}: set T. Admitted.
Definition set_singleton {T} (t: T): set T. Admitted.
Definition set_subset {T} (s1 s2: set T): bool. Admitted.
Definition set_union {T} (s1 s2: set T): set T. Admitted.

Obligation Tactic:=idtac.
Definition content_rt15_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt15_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt15_type T thiss1 := 
	content T thiss1 by rec 0 lt :=
	content T thiss1 := match thiss1 with
	| Nil_construct _ => @set_empty T
	| Cons_construct _ h1 t9 => 
			set_union (set_union (@set_empty T) (set_singleton h1)) (content T t9)
	end.

Hint Unfold content_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Obligation Tactic:=idtac.
Definition _forall_rt4_type (T: Type) (thiss8: List T) (p2: T -> bool) : Type :=
bool.

Fail Next Obligation.

Hint Unfold _forall_rt4_type.


Equations (noind) _forall (T: Type) (thiss8: List T) (p2: T -> bool) : _forall_rt4_type T thiss8 p2 := 
	_forall T thiss8 p2 by rec 0 lt :=
	_forall T thiss8 p2 := match thiss8 with
	| Nil_construct _ => true
	| Cons_construct _ h6 t45 => 
			ifthenelse (p2 h6) bool
				(fun _ => _forall T t45 p2 )
				(fun _ => false )
	end.

Hint Unfold _forall_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Obligation Tactic:=idtac.
Definition size_rt11_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt11_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt11_type T thiss30 := 
	size T thiss30 by rec 0 lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t130 => Z.add (1)%Z (proj1_sig (size T t130))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Obligation Tactic:=idtac.
Definition filter1_rt1_type (T: Type) (thiss40: List T) (p8: T -> bool) : Type :=
{res10: List T | (ifthenelse
	(ifthenelse (Z.leb (proj1_sig (size T res10)) (proj1_sig (size T thiss40))) bool
		(fun _ => set_subset (content T res10) (content T thiss40) )
		(fun _ => false ))
	bool
	(fun _ => _forall T res10 p8 )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold filter1_rt1_type.


Equations (noind) filter1 (T: Type) (thiss40: List T) (p8: T -> bool) : filter1_rt1_type T thiss40 p8 := 
	filter1 T thiss40 p8 by rec 0 lt :=
	filter1 T thiss40 p8 := ifthenelse (isNil _ thiss40) (List T)
		(fun _ => Nil_construct T )
		(fun _ => ifthenelse
			(ifthenelse (isCons _ thiss40) bool
				(fun _ => p8 (h T thiss40) )
				(fun _ => false ))
			(List T)
			(fun _ => Cons_construct T (h T thiss40) (proj1_sig (filter1 T (t4 T thiss40) p8)) )
			(fun _ => ifthenelse (isCons _ thiss40) (List T)
				(fun _ => proj1_sig (filter1 T (t4 T thiss40) p8) )
				(fun _ => let contradiction: False := _ in match contradiction with end ) ) ).

Hint Unfold filter1_comp_proj.

Timeout 10 Admit Obligations.
