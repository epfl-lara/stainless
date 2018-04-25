Load verif1.

Inductive Option (T: Type) :=
| None_construct: Option T
| Some_construct: T -> (Option T).

Program Definition isNone (T: Type) (src: Option T) : bool :=
match src with
| None_construct _ => true
| _ => false
end.
Fail Next Obligation.


Hint Unfold  isNone: recognizers. 

Program Definition isSome (T: Type) (src: Option T) : bool :=
match src with
| Some_construct _ _ => true
| _ => false
end.
Fail Next Obligation.


Hint Unfold  isSome: recognizers. 

Lemma None_exists: (forall T: Type, forall self: Option T, ((true = isNone T self)) <-> (((None_construct T = self)))). 
repeat t || autounfold with recognizers in * || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self1: Option T, ((true = isSome T self1)) <-> ((exists tmp: T, (Some_construct T tmp = self1)))). 
repeat t || autounfold with recognizers in * || eauto.
Qed.

Program Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.
Fail Next Obligation.


Hint Unfold  None_type: refinements. 

Program Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.
Fail Next Obligation.


Hint Unfold  Some_type: refinements. 

Ltac Option_tactic := match goal with 
| [ H: (true = isNone ?T ?self2) |- _ ] => poseNew (Mark (T,self2) "None_exists");pose proof ((proj1 (None_exists _ _)) H)
 | [ H: (isNone ?T ?self2 = true) |- _ ] => poseNew (Mark (T,self2) "None_exists");pose proof ((proj1 (None_exists _ _)) (eq_sym H))
 | [ H: (true = isSome ?T ?self3) |- _ ] => poseNew (Mark (T,self3) "Some_exists");pose proof ((proj1 (Some_exists _ _)) H)
 | [ H: (isSome ?T ?self3 = true) |- _ ] => poseNew (Mark (T,self3) "Some_exists");pose proof ((proj1 (Some_exists _ _)) (eq_sym H))
 | _ => t
end.
Ltac t1 := 
  t ||
  Option_tactic ||
  t_sets ||
  idtac ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t1.

Program Definition v (T: Type) (src: Some_type T) : T :=
match src with
| Some_construct _ f0 => f0
| _ => let contradiction: False := _ in match contradiction with end
end.
Fail Next Obligation.


Inductive List (T: Type) :=
| Cons_construct: T -> ((List T) -> (List T))
| Nil_construct: List T.

Program Definition isCons (T: Type) (src: List T) : bool :=
match src with
| Cons_construct _ _ _ => true
| _ => false
end.
Fail Next Obligation.


Hint Unfold  isCons: recognizers. 

Program Definition isNil (T: Type) (src: List T) : bool :=
match src with
| Nil_construct _ => true
| _ => false
end.
Fail Next Obligation.


Hint Unfold  isNil: recognizers. 

Lemma Cons_exists: (forall T: Type, forall self4: List T, ((true = isCons T self4)) <-> ((exists tmp2: List T, exists tmp1: T, (Cons_construct T tmp1 tmp2 = self4)))). 
repeat t || autounfold with recognizers in * || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self5: List T, ((true = isNil T self5)) <-> (((Nil_construct T = self5)))). 
repeat t || autounfold with recognizers in * || eauto.
Qed.

Program Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.
Fail Next Obligation.


Hint Unfold  Cons_type: refinements. 

Program Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.
Fail Next Obligation.


Hint Unfold  Nil_type: refinements. 

Ltac List_tactic := match goal with 
| [ H: (true = isCons ?T ?self6) |- _ ] => poseNew (Mark (T,self6) "Cons_exists");pose proof ((proj1 (Cons_exists _ _)) H)
 | [ H: (isCons ?T ?self6 = true) |- _ ] => poseNew (Mark (T,self6) "Cons_exists");pose proof ((proj1 (Cons_exists _ _)) (eq_sym H))
 | [ H: (true = isNil ?T ?self7) |- _ ] => poseNew (Mark (T,self7) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) H)
 | [ H: (isNil ?T ?self7 = true) |- _ ] => poseNew (Mark (T,self7) "Nil_exists");pose proof ((proj1 (Nil_exists _ _)) (eq_sym H))
 | _ => Option_tactic
end.
Ltac t2 := 
  t ||
  List_tactic ||
  t_sets ||
  idtac ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t2.
Program Definition h (T: Type) (src: Cons_type T) : T :=
match src with
| Cons_construct _ f0 f1 => f0
| _ => let contradiction: False := _ in match contradiction with end
end.
Fail Next Obligation.


Program Definition t3 (T: Type) (src: Cons_type T) : List T :=
match src with
| Cons_construct _ f0 f1 => f1
| _ => let contradiction: False := _ in match contradiction with end
end.
Fail Next Obligation.



Program Definition cons_ (T: Type) (thiss: List T) (t4: T) : List T :=
Cons_construct T t4 thiss.
Fail Next Obligation.


Hint Unfold cons_: definitions.
Program Definition T_type : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type.


Program Definition thiss1_type (T: T_type) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss1_type.


Program Definition content_rt_type (T: T_type) (thiss1: thiss1_type T) : Type :=
set (T).
Fail Next Obligation.


Hint Unfold content_rt_type.


Equations content (T: T_type) (thiss1: thiss1_type T)  : content_rt_type T thiss1 := 
content T thiss1 by rec ignore_termination lt :=
content T thiss1 := ifthenelse (isNil _ thiss1) (set (T)) (fun _ => @set_empty T ) (fun _ => ifthenelse (isCons _ thiss1) (set (T)) (fun _ => set_union (set_union (@set_empty T) (set_singleton (h T thiss1))) (content T (t3 T thiss1)) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold content_comp_proj.
Solve Obligations with (repeat t2).
Fail Next Obligation.

Ltac rwrtTac_1 := match goal with
  | H: context[content ?T ?l] |- _ =>
    poseNew (Mark (T,l) "content_equation");
    pose proof (content_equation_1 T l)
  | _ => idtac
end.

Ltac rwrtTac_2 := match goal with
  | |- context[content ?T ?l] =>
    poseNew (Mark (T,l) "content_equation");
    pose proof (content_equation_1 T l)
  | _ => idtac
end.

(*
Ltac rwrtTac :=
  match goal with
  | H: context[content ?T ?l] |- _ =>
    poseNew (Mark (T,l) "content_equation");
    pose proof (content_equation_1 T l)
  | |- context[content ?T ?l] =>
    poseNew (Mark (T,l) "content_equation");
    pose proof (content_equation_1 T l)
  end.*)


Ltac rwrtTac := progress (rwrtTac_1;rwrtTac_2).

Ltac t5 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t5.
Program Definition T_type1 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type1.


Program Definition thiss2_type (T: T_type1) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss2_type.


Program Definition v1_type (T: T_type1) (thiss2: thiss2_type T) : Type :=
T.
Fail Next Obligation.


Hint Unfold v1_type.


Program Definition contains_rt_type (T: T_type1) (thiss2: thiss2_type T) (v1: v1_type T thiss2) : Type :=
{x___2: bool | (Bool.eqb x___2 (set_elem_of v1 (content T thiss2)) = true)}.
Fail Next Obligation.


Hint Unfold contains_rt_type.


Equations contains (T: T_type1) (thiss2: thiss2_type T) (v1: v1_type T thiss2)  : contains_rt_type T thiss2 v1 := 
contains T thiss2 v1 by rec ignore_termination lt :=
contains T thiss2 v1 := ifthenelse (isCons _ thiss2) bool (fun _ => propInBool ((h T thiss2 = v1)) || contains T (t3 T thiss2) v1 ) (fun _ => ifthenelse (isNil _ thiss2) bool (fun _ => false ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold contains_comp_proj.

Obligation Tactic := idtac.

Next Obligation. repeat t5. Qed.
Next Obligation.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  t5.
  (* here *)
  t5.
  t5.
  repeat t5.

  
Solve Obligations with (repeat t5).
Fail Next Obligation.
Ltac rwrtTac1 := rwrtTac
  || rewrite contains_equation_1 in *.
Ltac t6 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac1 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t6.
Program Definition empty (A: Type) (B: Type) : map_type A (Option B) :=
magic (map_type A (Option B)).
Fail Next Obligation.


Hint Unfold empty: definitions.
Program Definition filter (T: Type) (thiss3: Option T) (p: T -> bool) : Option T :=
ifthenelse (ifthenelse (isSome _ thiss3) bool (fun _ => p (v T thiss3) ) (fun _ => false )) (Option T) (fun _ => Some_construct T (v T thiss3) ) (fun _ => None_construct T ).
Fail Next Obligation.


Hint Unfold filter: definitions.
Program Definition T_type2 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type2.


Program Definition thiss4_type (T: T_type2) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss4_type.


Program Definition p1_type (T: T_type2) (thiss4: thiss4_type T) : Type :=
T -> bool.
Fail Next Obligation.


Hint Unfold p1_type.


Program Definition find_rt_type (T: T_type2) (thiss4: thiss4_type T) (p1: p1_type T thiss4) : Type :=
{res: Option T | (ifthenelse (isSome _ res) bool (fun _ => ifthenelse (set_elem_of (v T res) (content T thiss4)) bool (fun _ => p1 (v T res) ) (fun _ => false ) ) (fun _ => ifthenelse (isNone _ res) bool (fun _ => true ) (fun _ => let contradiction: False := _ in match contradiction with end ) ) = true)}.
Fail Next Obligation.


Hint Unfold find_rt_type.


Equations find (T: T_type2) (thiss4: thiss4_type T) (p1: p1_type T thiss4)  : find_rt_type T thiss4 p1 := 
find T thiss4 p1 by rec ignore_termination lt :=
find T thiss4 p1 := ifthenelse (isNil _ thiss4) (Option T) (fun _ => None_construct T ) (fun _ => ifthenelse (isCons _ thiss4) (Option T) (fun _ => ifthenelse (p1 (h T thiss4)) (Option T) (fun _ => Some_construct T (h T thiss4) ) (fun _ => find T (t3 T thiss4) p1 ) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold find_comp_proj.
Solve Obligations with (repeat t6).
Fail Next Obligation.
Ltac rwrtTac2 := rwrtTac1
  || rewrite find_equation_1 in *.
Ltac t7 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac2 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t7.
Program Definition flatMap (T: Type) (R: Type) (thiss5: Option T) (f: T -> (Option R)) : Option R :=
ifthenelse (isNone _ thiss5) (Option R) (fun _ => None_construct R ) (fun _ => ifthenelse (isSome _ thiss5) (Option R) (fun _ => f (v T thiss5) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).
Fail Next Obligation.


Hint Unfold flatMap: definitions.
Program Definition T_type3 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type3.


Program Definition R_type (T: T_type3) : Type :=
Type.
Fail Next Obligation.


Hint Unfold R_type.


Program Definition thiss6_type (T: T_type3) (R: R_type T) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss6_type.


Program Definition z_type (T: T_type3) (R: R_type T) (thiss6: thiss6_type T R) : Type :=
R.
Fail Next Obligation.


Hint Unfold z_type.


Program Definition f1_type (T: T_type3) (R: R_type T) (thiss6: thiss6_type T R) (z: z_type T R thiss6) : Type :=
R -> (T -> R).
Fail Next Obligation.


Hint Unfold f1_type.


Program Definition foldLeft_rt_type (T: T_type3) (R: R_type T) (thiss6: thiss6_type T R) (z: z_type T R thiss6) (f1: f1_type T R thiss6 z) : Type :=
R.
Fail Next Obligation.


Hint Unfold foldLeft_rt_type.


Equations foldLeft (T: T_type3) (R: R_type T) (thiss6: thiss6_type T R) (z: z_type T R thiss6) (f1: f1_type T R thiss6 z)  : foldLeft_rt_type T R thiss6 z f1 := 
foldLeft T R thiss6 z f1 by rec ignore_termination lt :=
foldLeft T R thiss6 z f1 := ifthenelse (isNil _ thiss6) R (fun _ => z ) (fun _ => ifthenelse (isCons _ thiss6) R (fun _ => foldLeft T R (t3 T thiss6) (f1 z (h T thiss6)) f1 ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold foldLeft_comp_proj.
Solve Obligations with (repeat t7).
Fail Next Obligation.
Ltac rwrtTac3 := rwrtTac2
  || rewrite foldLeft_equation_1 in *.
Ltac t8 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac3 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t8.
Program Definition T_type4 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type4.


Program Definition R_type1 (T: T_type4) : Type :=
Type.
Fail Next Obligation.


Hint Unfold R_type1.


Program Definition thiss7_type (T: T_type4) (R: R_type1 T) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss7_type.


Program Definition z1_type (T: T_type4) (R: R_type1 T) (thiss7: thiss7_type T R) : Type :=
R.
Fail Next Obligation.


Hint Unfold z1_type.


Program Definition f2_type (T: T_type4) (R: R_type1 T) (thiss7: thiss7_type T R) (z1: z1_type T R thiss7) : Type :=
T -> (R -> R).
Fail Next Obligation.


Hint Unfold f2_type.


Program Definition foldRight_rt_type (T: T_type4) (R: R_type1 T) (thiss7: thiss7_type T R) (z1: z1_type T R thiss7) (f2: f2_type T R thiss7 z1) : Type :=
R.
Fail Next Obligation.


Hint Unfold foldRight_rt_type.


Equations foldRight (T: T_type4) (R: R_type1 T) (thiss7: thiss7_type T R) (z1: z1_type T R thiss7) (f2: f2_type T R thiss7 z1)  : foldRight_rt_type T R thiss7 z1 f2 := 
foldRight T R thiss7 z1 f2 by rec ignore_termination lt :=
foldRight T R thiss7 z1 f2 := ifthenelse (isNil _ thiss7) R (fun _ => z1 ) (fun _ => ifthenelse (isCons _ thiss7) R (fun _ => f2 (h T thiss7) (foldRight T R (t3 T thiss7) z1 f2) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold foldRight_comp_proj.
Solve Obligations with (repeat t8).
Fail Next Obligation.
Ltac rwrtTac4 := rwrtTac3
  || rewrite foldRight_equation_1 in *.
Ltac t9 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac4 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t9.
Program Definition _forall (T: Type) (thiss8: Option T) (p2: T -> bool) : bool :=
ifthenelse (ifthenelse (isSome _ thiss8) bool (fun _ => negb (p2 (v T thiss8)) ) (fun _ => false )) bool (fun _ => false ) (fun _ => true ).
Fail Next Obligation.


Hint Unfold _forall: definitions.
Program Definition _exists (T: Type) (thiss9: Option T) (p3: T -> bool) : bool :=
negb (_forall T thiss9 (fun x___3 => negb (p3 x___3) )).
Fail Next Obligation.


Hint Unfold _exists: definitions.
Program Definition T_type5 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type5.


Program Definition thiss10_type (T: T_type5) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss10_type.


Program Definition p4_type (T: T_type5) (thiss10: thiss10_type T) : Type :=
T -> bool.
Fail Next Obligation.


Hint Unfold p4_type.


Program Definition forall1_rt_type (T: T_type5) (thiss10: thiss10_type T) (p4: p4_type T thiss10) : Type :=
bool.
Fail Next Obligation.


Hint Unfold forall1_rt_type.


Equations forall1 (T: T_type5) (thiss10: thiss10_type T) (p4: p4_type T thiss10)  : forall1_rt_type T thiss10 p4 := 
forall1 T thiss10 p4 by rec ignore_termination lt :=
forall1 T thiss10 p4 := ifthenelse (isNil _ thiss10) bool (fun _ => true ) (fun _ => ifthenelse (isCons _ thiss10) bool (fun _ => ifthenelse (p4 (h T thiss10)) bool (fun _ => forall1 T (t3 T thiss10) p4 ) (fun _ => false ) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold forall1_comp_proj.
Solve Obligations with (repeat t9).
Fail Next Obligation.
Ltac rwrtTac5 := rwrtTac4
  || rewrite forall1_equation_1 in *.
Ltac t10 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac5 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t10.
Program Definition exists1 (T: Type) (thiss11: List T) (p5: T -> bool) : bool :=
negb (forall1 T thiss11 (fun x___22 => negb (p5 x___22) )).
Fail Next Obligation.


Hint Unfold exists1: definitions.
Program Definition getOrElse (T: Type) (thiss12: Option T) (default: T) : T :=
ifthenelse (isSome _ thiss12) T (fun _ => v T thiss12 ) (fun _ => ifthenelse (isNone _ thiss12) T (fun _ => default ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).
Fail Next Obligation.


Hint Unfold getOrElse: definitions.
Program Definition T_type6 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type6.


Program Definition R_type2 (T: T_type6) : Type :=
Type.
Fail Next Obligation.


Hint Unfold R_type2.


Program Definition thiss13_type (T: T_type6) (R: R_type2 T) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss13_type.


Program Definition f3_type (T: T_type6) (R: R_type2 T) (thiss13: thiss13_type T R) : Type :=
T -> R.
Fail Next Obligation.


Hint Unfold f3_type.


Program Definition groupBy_rt_type (T: T_type6) (R: R_type2 T) (thiss13: thiss13_type T R) (f3: f3_type T R thiss13) : Type :=
map_type R (Option (List T)).
Fail Next Obligation.


Hint Unfold groupBy_rt_type.


Equations groupBy (T: T_type6) (R: R_type2 T) (thiss13: thiss13_type T R) (f3: f3_type T R thiss13)  : groupBy_rt_type T R thiss13 f3 := 
groupBy T R thiss13 f3 by rec ignore_termination lt :=
groupBy T R thiss13 f3 := ifthenelse (isNil _ thiss13) (map_type R (Option (List T))) (fun _ => magic (map_type R (Option (List T))) ) (fun _ => ifthenelse (isCons _ thiss13) (map_type R (Option (List T))) (fun _ => let key := (f3 (h T thiss13)) in (let rest := (groupBy T R (t3 T thiss13) f3) in (let prev := (ifthenelse (negb (propInBool ((magic (Option (List T)) = None_construct (List T))))) (List T) (fun _ => magic (List T) ) (fun _ => Nil_construct T )) in (magic (map_type R (Option (List T)))))) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold groupBy_comp_proj.
Solve Obligations with (repeat t10).
Fail Next Obligation.
Ltac rwrtTac6 := rwrtTac5
  || rewrite groupBy_equation_1 in *.
Ltac t11 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac6 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t11.
Program Definition head (T: Type) (thiss14: List T) (contractHyp16: (negb (propInBool ((thiss14 = Nil_construct T))) = true)) : T :=
ifthenelse (isCons _ thiss14) T (fun _ => h T thiss14 ) (fun _ => let contradiction: False := _ in match contradiction with end ).
Fail Next Obligation.


Hint Unfold head: definitions.
Program Definition T_type7 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type7.


Program Definition thiss15_type (T: T_type7) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss15_type.


Program Definition elem_type (T: T_type7) (thiss15: thiss15_type T) : Type :=
T.
Fail Next Obligation.


Hint Unfold elem_type.


Program Definition indexOf_rt_type (T: T_type7) (thiss15: thiss15_type T) (elem: elem_type T thiss15) : Type :=
{res1: Z | (Bool.eqb (Z.geb res1 (0)%Z) (set_elem_of elem (content T thiss15)) = true)}.
Fail Next Obligation.


Hint Unfold indexOf_rt_type.


Equations indexOf (T: T_type7) (thiss15: thiss15_type T) (elem: elem_type T thiss15)  : indexOf_rt_type T thiss15 elem := 
indexOf T thiss15 elem by rec ignore_termination lt :=
indexOf T thiss15 elem := ifthenelse (isNil _ thiss15) Z (fun _ => (-1)%Z ) (fun _ => ifthenelse (ifthenelse (isCons _ thiss15) bool (fun _ => propInBool ((h T thiss15 = elem)) ) (fun _ => false )) Z (fun _ => (0)%Z ) (fun _ => ifthenelse (isCons _ thiss15) Z (fun _ => let rec := (indexOf T (t3 T thiss15) elem) in (ifthenelse (Zeq_bool rec (-1)%Z) Z (fun _ => (-1)%Z ) (fun _ => Z.add rec (1)%Z )) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ) ).

Hint Unfold indexOf_comp_proj.
Solve Obligations with (repeat t11).
Fail Next Obligation.
Ltac rwrtTac7 := rwrtTac6
  || rewrite indexOf_equation_1 in *.
Ltac t12 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac7 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t12.
Program Definition T_type8 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type8.


Program Definition thiss16_type (T: T_type8) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss16_type.


Program Definition p6_type (T: T_type8) (thiss16: thiss16_type T) : Type :=
T -> bool.
Fail Next Obligation.


Hint Unfold p6_type.


Program Definition indexWhere_rt_type (T: T_type8) (thiss16: thiss16_type T) (p6: p6_type T thiss16) : Type :=
{x___25: Z | (Bool.eqb (Z.geb x___25 (0)%Z) (exists1 T thiss16 p6) = true)}.
Fail Next Obligation.


Hint Unfold indexWhere_rt_type.


Equations indexWhere (T: T_type8) (thiss16: thiss16_type T) (p6: p6_type T thiss16)  : indexWhere_rt_type T thiss16 p6 := 
indexWhere T thiss16 p6 by rec ignore_termination lt :=
indexWhere T thiss16 p6 := ifthenelse (isNil _ thiss16) Z (fun _ => (-1)%Z ) (fun _ => ifthenelse (ifthenelse (isCons _ thiss16) bool (fun _ => p6 (h T thiss16) ) (fun _ => false )) Z (fun _ => (0)%Z ) (fun _ => ifthenelse (isCons _ thiss16) Z (fun _ => let rec1 := (indexWhere T (t3 T thiss16) p6) in (ifthenelse (Z.geb rec1 (0)%Z) Z (fun _ => Z.add rec1 (1)%Z ) (fun _ => (-1)%Z )) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ) ).

Hint Unfold indexWhere_comp_proj.
Solve Obligations with (repeat t12).
Fail Next Obligation.
Ltac rwrtTac8 := rwrtTac7
  || rewrite indexWhere_equation_1 in *.
Ltac t13 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac8 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t13.
Program Definition isEmpty (T: Type) (thiss17: List T) : bool :=
ifthenelse (isNil _ thiss17) bool (fun _ => true ) (fun _ => false ).
Fail Next Obligation.


Hint Unfold isEmpty: definitions.
Program Definition isEmpty1 (T: Type) (thiss18: Option T) : bool :=
propInBool ((thiss18 = None_construct T)).
Fail Next Obligation.


Hint Unfold isEmpty1: definitions.
Program Definition isDefined (T: Type) (thiss19: Option T) : bool :=
negb (isEmpty1 T thiss19).
Fail Next Obligation.


Hint Unfold isDefined: definitions.
Program Definition get (T: Type) (thiss20: Option T) (contractHyp22: (isDefined T thiss20 = true)) : T :=
ifthenelse (isSome _ thiss20) T (fun _ => v T thiss20 ) (fun _ => let contradiction: False := _ in match contradiction with end ).
Fail Next Obligation.


Hint Unfold get: definitions.
Program Definition headOption (T: Type) (thiss21: List T) : {x___5: Option T | (negb (Bool.eqb (isDefined T x___5) (isEmpty T thiss21)) = true)} :=
ifthenelse (isCons _ thiss21) (Option T) (fun _ => Some_construct T (h T thiss21) ) (fun _ => ifthenelse (isNil _ thiss21) (Option T) (fun _ => None_construct T ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).
Fail Next Obligation.


Hint Unfold headOption: definitions.
Program Definition T_type9 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type9.


Program Definition thiss22_type (T: T_type9) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss22_type.


Program Definition contractHyp24_type (T: T_type9) (thiss22: thiss22_type T) : Type :=
(negb (isEmpty T thiss22) = true).
Fail Next Obligation.


Hint Unfold contractHyp24_type.


Program Definition last_rt_type (T: T_type9) (thiss22: thiss22_type T) (contractHyp24: contractHyp24_type T thiss22) : Type :=
{v2: T | (contains T thiss22 v2 = true)}.
Fail Next Obligation.


Hint Unfold last_rt_type.


Equations last (T: T_type9) (thiss22: thiss22_type T) (contractHyp24: contractHyp24_type T thiss22)  : last_rt_type T thiss22 contractHyp24 := 
last T thiss22 contractHyp24 by rec ignore_termination lt :=
last T thiss22 contractHyp24 := ifthenelse (ifthenelse (isCons _ thiss22) bool (fun _ => isNil _ (t3 T thiss22) ) (fun _ => false )) T (fun _ => h T thiss22 ) (fun _ => ifthenelse (isCons _ thiss22) T (fun _ => last T (t3 T thiss22) _ ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold last_comp_proj.
Solve Obligations with (repeat t13).
Fail Next Obligation.
Ltac rwrtTac9 := rwrtTac8
  || rewrite last_equation_1 in *.
Ltac t14 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac9 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t14.
Program Definition map (T: Type) (R: Type) (thiss23: Option T) (f4: T -> R) : {x___21: Option R | (Bool.eqb (isDefined R x___21) (isDefined T thiss23) = true)} :=
ifthenelse (isNone _ thiss23) (Option R) (fun _ => None_construct R ) (fun _ => ifthenelse (isSome _ thiss23) (Option R) (fun _ => Some_construct R (f4 (v T thiss23)) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).
Fail Next Obligation.


Hint Unfold map: definitions.
Program Definition nonEmpty (T: Type) (thiss24: Option T) : bool :=
negb (isEmpty1 T thiss24).
Fail Next Obligation.


Hint Unfold nonEmpty: definitions.
Program Definition nonEmpty1 (T: Type) (thiss25: List T) : bool :=
negb (isEmpty T thiss25).
Fail Next Obligation.


Hint Unfold nonEmpty1: definitions.
Program Definition orElse (T: Type) (thiss26: Option T) (or: Option T) : {x___1: Option T | (Bool.eqb (isDefined T x___1) (isDefined T thiss26) || isDefined T or = true)} :=
ifthenelse (isSome _ thiss26) (Option T) (fun _ => thiss26 ) (fun _ => ifthenelse (isNone _ thiss26) (Option T) (fun _ => or ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).
Fail Next Obligation.


Hint Unfold orElse: definitions.
Program Definition T_type10 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type10.


Program Definition thiss27_type (T: T_type10) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss27_type.


Program Definition lastOption_rt_type (T: T_type10) (thiss27: thiss27_type T) : Type :=
{x___4: Option T | (negb (Bool.eqb (isDefined T x___4) (isEmpty T thiss27)) = true)}.
Fail Next Obligation.


Hint Unfold lastOption_rt_type.


Equations lastOption (T: T_type10) (thiss27: thiss27_type T)  : lastOption_rt_type T thiss27 := 
lastOption T thiss27 by rec ignore_termination lt :=
lastOption T thiss27 := ifthenelse (isCons _ thiss27) (Option T) (fun _ => orElse T (lastOption T (t3 T thiss27)) (Some_construct T (h T thiss27)) ) (fun _ => ifthenelse (isNil _ thiss27) (Option T) (fun _ => None_construct T ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold lastOption_comp_proj.
Solve Obligations with (repeat t14).
Fail Next Obligation.
Ltac rwrtTac10 := rwrtTac9
  || rewrite lastOption_equation_1 in *.
Ltac t15 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac10 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t15.
Program Definition T_type11 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type11.


Program Definition R_type3 (T: T_type11) : Type :=
Type.
Fail Next Obligation.


Hint Unfold R_type3.


Program Definition thiss28_type (T: T_type11) (R: R_type3 T) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss28_type.


Program Definition z2_type (T: T_type11) (R: R_type3 T) (thiss28: thiss28_type T R) : Type :=
R.
Fail Next Obligation.


Hint Unfold z2_type.


Program Definition f5_type (T: T_type11) (R: R_type3 T) (thiss28: thiss28_type T R) (z2: z2_type T R thiss28) : Type :=
R -> (T -> R).
Fail Next Obligation.


Hint Unfold f5_type.


Program Definition scanLeft_rt_type (T: T_type11) (R: R_type3 T) (thiss28: thiss28_type T R) (z2: z2_type T R thiss28) (f5: f5_type T R thiss28 z2) : Type :=
{x___12: List R | (negb (isEmpty R x___12) = true)}.
Fail Next Obligation.


Hint Unfold scanLeft_rt_type.


Equations scanLeft (T: T_type11) (R: R_type3 T) (thiss28: thiss28_type T R) (z2: z2_type T R thiss28) (f5: f5_type T R thiss28 z2)  : scanLeft_rt_type T R thiss28 z2 f5 := 
scanLeft T R thiss28 z2 f5 by rec ignore_termination lt :=
scanLeft T R thiss28 z2 f5 := ifthenelse (isNil _ thiss28) (List R) (fun _ => cons_ R (Nil_construct R) z2 ) (fun _ => ifthenelse (isCons _ thiss28) (List R) (fun _ => cons_ R (scanLeft T R (t3 T thiss28) (f5 z2 (h T thiss28)) f5) z2 ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold scanLeft_comp_proj.
Solve Obligations with (repeat t15).
Fail Next Obligation.
Ltac rwrtTac11 := rwrtTac10
  || rewrite scanLeft_equation_1 in *.
Ltac t16 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac11 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t16.
Program Definition T_type12 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type12.


Program Definition R_type4 (T: T_type12) : Type :=
Type.
Fail Next Obligation.


Hint Unfold R_type4.


Program Definition thiss29_type (T: T_type12) (R: R_type4 T) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss29_type.


Program Definition z3_type (T: T_type12) (R: R_type4 T) (thiss29: thiss29_type T R) : Type :=
R.
Fail Next Obligation.


Hint Unfold z3_type.


Program Definition f6_type (T: T_type12) (R: R_type4 T) (thiss29: thiss29_type T R) (z3: z3_type T R thiss29) : Type :=
T -> (R -> R).
Fail Next Obligation.


Hint Unfold f6_type.


Program Definition scanRight_rt_type (T: T_type12) (R: R_type4 T) (thiss29: thiss29_type T R) (z3: z3_type T R thiss29) (f6: f6_type T R thiss29 z3) : Type :=
{x___16: List R | (negb (isEmpty R x___16) = true)}.
Fail Next Obligation.


Hint Unfold scanRight_rt_type.


Equations scanRight (T: T_type12) (R: R_type4 T) (thiss29: thiss29_type T R) (z3: z3_type T R thiss29) (f6: f6_type T R thiss29 z3)  : scanRight_rt_type T R thiss29 z3 f6 := 
scanRight T R thiss29 z3 f6 by rec ignore_termination lt :=
scanRight T R thiss29 z3 f6 := ifthenelse (isNil _ thiss29) (List R) (fun _ => cons_ R (Nil_construct R) z3 ) (fun _ => ifthenelse (isCons _ thiss29) (List R) (fun _ => let x___14 := (ifthenelse (isCons _ (scanRight T R (t3 T thiss29) z3 f6)) (((List R) * R)%type) (fun _ => (scanRight T R (t3 T thiss29) z3 f6,h R (scanRight T R (t3 T thiss29) z3 f6)) ) (fun _ => let contradiction: False := _ in match contradiction with end )) in (let h1 := (snd x___14) in (let x___15 := (f6 (h T thiss29) h1) in (cons_ R (fst x___14) x___15))) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold scanRight_comp_proj.
Solve Obligations with (repeat t16).
Fail Next Obligation.
Ltac rwrtTac12 := rwrtTac11
  || rewrite scanRight_equation_1 in *.
Ltac t17 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac12 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t17.
Program Definition T_type13 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type13.


Program Definition thiss30_type (T: T_type13) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss30_type.


Program Definition size_rt_type (T: T_type13) (thiss30: thiss30_type T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.
Fail Next Obligation.


Hint Unfold size_rt_type.


Equations size (T: T_type13) (thiss30: thiss30_type T)  : size_rt_type T thiss30 := 
size T thiss30 by rec ignore_termination lt :=
size T thiss30 := ifthenelse (isNil _ thiss30) Z (fun _ => (0)%Z ) (fun _ => ifthenelse (isCons _ thiss30) Z (fun _ => Z.add (1)%Z (size T (t3 T thiss30)) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold size_comp_proj.
Solve Obligations with (repeat t17).
Fail Next Obligation.
Ltac rwrtTac13 := rwrtTac12
  || rewrite size_equation_1 in *.
Ltac t18 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac13 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t18.
Program Definition T_type14 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type14.


Program Definition thiss31_type (T: T_type14) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss31_type.


Program Definition that_type (T: T_type14) (thiss31: thiss31_type T) : Type :=
List T.
Fail Next Obligation.


Hint Unfold that_type.


Program Definition c__rt_type (T: T_type14) (thiss31: thiss31_type T) (that: that_type T thiss31) : Type :=
{res2: List T | (ifthenelse (Z.leb (size T res2) (size T thiss31)) bool (fun _ => set_equality (content T res2) (set_intersection (content T thiss31) (content T that)) ) (fun _ => false ) = true)}.
Fail Next Obligation.


Hint Unfold c__rt_type.


Equations c_ (T: T_type14) (thiss31: thiss31_type T) (that: that_type T thiss31)  : c__rt_type T thiss31 that := 
c_ T thiss31 that by rec ignore_termination lt :=
c_ T thiss31 that := ifthenelse (isCons _ thiss31) (List T) (fun _ => ifthenelse (contains T that (h T thiss31)) (List T) (fun _ => Cons_construct T (h T thiss31) (c_ T (t3 T thiss31) that) ) (fun _ => c_ T (t3 T thiss31) that ) ) (fun _ => ifthenelse (isNil _ thiss31) (List T) (fun _ => Nil_construct T ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold c__comp_proj.
Solve Obligations with (repeat t18).
Fail Next Obligation.
Ltac rwrtTac14 := rwrtTac13
  || rewrite c__equation_1 in *.
Ltac t19 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac14 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t19.
Program Definition T_type15 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type15.


Program Definition thiss32_type (T: T_type15) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss32_type.


Program Definition that1_type (T: T_type15) (thiss32: thiss32_type T) : Type :=
List T.
Fail Next Obligation.


Hint Unfold that1_type.


Program Definition plus_plus__rt_type (T: T_type15) (thiss32: thiss32_type T) (that1: that1_type T thiss32) : Type :=
{res3: List T | (ifthenelse (ifthenelse (set_equality (content T res3) (set_union (content T thiss32) (content T that1))) bool (fun _ => Zeq_bool (size T res3) (Z.add (size T thiss32) (size T that1)) ) (fun _ => false )) bool (fun _ => negb (propInBool ((that1 = Nil_construct T))) || propInBool ((res3 = thiss32)) ) (fun _ => false ) = true)}.
Fail Next Obligation.


Hint Unfold plus_plus__rt_type.


Equations plus_plus_ (T: T_type15) (thiss32: thiss32_type T) (that1: that1_type T thiss32)  : plus_plus__rt_type T thiss32 that1 := 
plus_plus_ T thiss32 that1 by rec ignore_termination lt :=
plus_plus_ T thiss32 that1 := ifthenelse (isNil _ thiss32) (List T) (fun _ => that1 ) (fun _ => ifthenelse (isCons _ thiss32) (List T) (fun _ => Cons_construct T (h T thiss32) (plus_plus_ T (t3 T thiss32) that1) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold plus_plus__comp_proj.
Solve Obligations with (repeat t19).
Fail Next Obligation.
Ltac rwrtTac15 := rwrtTac14
  || rewrite plus_plus__equation_1 in *.
Ltac t20 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac15 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t20.
Program Definition T_type16 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type16.


Program Definition thiss33_type (T: T_type16) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss33_type.


Program Definition e_type (T: T_type16) (thiss33: thiss33_type T) : Type :=
T.
Fail Next Obligation.


Hint Unfold e_type.


Program Definition minus__rt_type (T: T_type16) (thiss33: thiss33_type T) (e: e_type T thiss33) : Type :=
{res4: List T | (ifthenelse (Z.leb (size T res4) (size T thiss33)) bool (fun _ => set_equality (content T res4) (set_difference (content T thiss33) (set_union (@set_empty T) (set_singleton e))) ) (fun _ => false ) = true)}.
Fail Next Obligation.


Hint Unfold minus__rt_type.


Equations minus_ (T: T_type16) (thiss33: thiss33_type T) (e: e_type T thiss33)  : minus__rt_type T thiss33 e := 
minus_ T thiss33 e by rec ignore_termination lt :=
minus_ T thiss33 e := ifthenelse (isCons _ thiss33) (List T) (fun _ => ifthenelse (propInBool ((e = h T thiss33))) (List T) (fun _ => minus_ T (t3 T thiss33) e ) (fun _ => Cons_construct T (h T thiss33) (minus_ T (t3 T thiss33) e) ) ) (fun _ => ifthenelse (isNil _ thiss33) (List T) (fun _ => Nil_construct T ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold minus__comp_proj.
Solve Obligations with (repeat t20).
Fail Next Obligation.
Ltac rwrtTac16 := rwrtTac15
  || rewrite minus__equation_1 in *.
Ltac t21 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac16 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t21.
Program Definition T_type17 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type17.


Program Definition thiss34_type (T: T_type17) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss34_type.


Program Definition that2_type (T: T_type17) (thiss34: thiss34_type T) : Type :=
List T.
Fail Next Obligation.


Hint Unfold that2_type.


Program Definition substract__rt_type (T: T_type17) (thiss34: thiss34_type T) (that2: that2_type T thiss34) : Type :=
{res5: List T | (ifthenelse (Z.leb (size T res5) (size T thiss34)) bool (fun _ => set_equality (content T res5) (set_difference (content T thiss34) (content T that2)) ) (fun _ => false ) = true)}.
Fail Next Obligation.


Hint Unfold substract__rt_type.


Equations substract_ (T: T_type17) (thiss34: thiss34_type T) (that2: that2_type T thiss34)  : substract__rt_type T thiss34 that2 := 
substract_ T thiss34 that2 by rec ignore_termination lt :=
substract_ T thiss34 that2 := ifthenelse (isCons _ thiss34) (List T) (fun _ => ifthenelse (contains T that2 (h T thiss34)) (List T) (fun _ => substract_ T (t3 T thiss34) that2 ) (fun _ => Cons_construct T (h T thiss34) (substract_ T (t3 T thiss34) that2) ) ) (fun _ => ifthenelse (isNil _ thiss34) (List T) (fun _ => Nil_construct T ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold substract__comp_proj.
Solve Obligations with (repeat t21).
Fail Next Obligation.
Ltac rwrtTac17 := rwrtTac16
  || rewrite substract__equation_1 in *.
Ltac t22 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac17 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t22.
Program Definition T_type18 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type18.


Program Definition thiss35_type (T: T_type18) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss35_type.


Program Definition t23_type (T: T_type18) (thiss35: thiss35_type T) : Type :=
T.
Fail Next Obligation.


Hint Unfold t23_type.


Program Definition snoc__rt_type (T: T_type18) (thiss35: thiss35_type T) (t23: t23_type T thiss35) : Type :=
{res6: List T | (magic bool = true)}.
Fail Next Obligation.


Hint Unfold snoc__rt_type.


Equations snoc_ (T: T_type18) (thiss35: thiss35_type T) (t23: t23_type T thiss35)  : snoc__rt_type T thiss35 t23 := 
snoc_ T thiss35 t23 by rec ignore_termination lt :=
snoc_ T thiss35 t23 := ifthenelse (isNil _ thiss35) (List T) (fun _ => Cons_construct T t23 thiss35 ) (fun _ => ifthenelse (isCons _ thiss35) (List T) (fun _ => Cons_construct T (h T thiss35) (snoc_ T (t3 T thiss35) t23) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold snoc__comp_proj.
Solve Obligations with (repeat t22).
Fail Next Obligation.
Ltac rwrtTac18 := rwrtTac17
  || rewrite snoc__equation_1 in *.
Ltac t24 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac18 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t24.
Program Definition T_type19 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type19.


Program Definition thiss36_type (T: T_type19) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss36_type.


Program Definition s_type (T: T_type19) (thiss36: thiss36_type T) (s: s_type T thiss36 s l acc res7) (l: s_type T thiss36 s l acc res7) (acc: s_type T thiss36 s l acc res7) (res7: res7_type T thiss36 s l acc) : Type :=
Z.
Fail Next Obligation.


Hint Unfold s_type.


Program Definition s_type (T: T_type19) (thiss36: thiss36_type T) (s: s_type T thiss36 s l acc res7) (l: s_type T thiss36 s l acc res7) (acc: s_type T thiss36 s l acc res7) (res7: res7_type T thiss36 s l acc) : Type :=
List T.
Fail Next Obligation.


Hint Unfold s_type.


Program Definition s_type (T: T_type19) (thiss36: thiss36_type T) (s: s_type T thiss36 s l acc res7) (l: s_type T thiss36 s l acc res7) (acc: s_type T thiss36 s l acc res7) (res7: res7_type T thiss36 s l acc) : Type :=
List T.
Fail Next Obligation.


Hint Unfold s_type.


Program Definition res7_type (T: T_type19) (thiss36: thiss36_type T) (s: s_type T thiss36 s l acc res7) (l: s_type T thiss36 s l acc res7) (acc: s_type T thiss36 s l acc res7) : Type :=
List (List T).
Fail Next Obligation.


Hint Unfold res7_type.


Program Definition s_type (T: T_type19) (thiss36: thiss36_type T) (s: s_type T thiss36 s l acc res7) (l: s_type T thiss36 s l acc res7) (acc: s_type T thiss36 s l acc res7) (res7: res7_type T thiss36 s l acc) : Type :=
Z.
Fail Next Obligation.


Hint Unfold s_type.


Program Definition contractHyp38_type (T: T_type19) (thiss36: thiss36_type T) (s: s_type T thiss36 s l acc res7) (l: s_type T thiss36 s l acc res7) (acc: s_type T thiss36 s l acc res7) (res7: res7_type T thiss36 s l acc) (s0: s_type T thiss36 s l acc res7) : Type :=
(ifthenelse (Z.gtb s (0)%Z) bool (fun _ => Z.geb s0 (0)%Z ) (fun _ => false ) = true).
Fail Next Obligation.


Hint Unfold contractHyp38_type.


Program Definition chunk0_rt_type (T: T_type19) (thiss36: thiss36_type T) (s: s_type T thiss36 s l acc res7) (l: s_type T thiss36 s l acc res7) (acc: s_type T thiss36 s l acc res7) (res7: res7_type T thiss36 s l acc) (s0: s_type T thiss36 s l acc res7) (contractHyp38: contractHyp38_type T thiss36 s l acc res7 s0) : Type :=
List (List T).
Fail Next Obligation.


Hint Unfold chunk0_rt_type.


Equations chunk0 (T: T_type19) (thiss36: thiss36_type T) (s: s_type T thiss36 s l acc res7) (l: s_type T thiss36 s l acc res7) (acc: s_type T thiss36 s l acc res7) (res7: res7_type T thiss36 s l acc) (s0: s_type T thiss36 s l acc res7) (contractHyp38: contractHyp38_type T thiss36 s l acc res7 s0)  : chunk0_rt_type T thiss36 s l acc res7 s0 contractHyp38 := 
chunk0 T thiss36 s l acc res7 s0 contractHyp38 by rec ignore_termination lt :=
chunk0 T thiss36 s l acc res7 s0 contractHyp38 := ifthenelse (isNil _ l) (List (List T)) (fun _ => ifthenelse (Z.gtb (size T acc) (0)%Z) (List (List T)) (fun _ => snoc_ (List T) res7 acc ) (fun _ => res7 ) ) (fun _ => ifthenelse (isCons _ l) (List (List T)) (fun _ => ifthenelse (Zeq_bool s0 (0)%Z) (List (List T)) (fun _ => chunk0 T thiss36 s (t3 T l) (Cons_construct T (h T l) (Nil_construct T)) (snoc_ (List T) res7 acc) (Z.sub s (1)%Z) _ ) (fun _ => chunk0 T thiss36 s (t3 T l) (snoc_ T acc (h T l)) res7 (Z.sub s0 (1)%Z) _ ) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold chunk0_comp_proj.
Solve Obligations with (repeat t24).
Fail Next Obligation.
Ltac rwrtTac19 := rwrtTac18
  || rewrite chunk0_equation_1 in *.
Ltac t25 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac19 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t25.
Program Definition chunks (T: Type) (thiss37: List T) (s1: Z) (contractHyp39: (Z.gtb s1 (0)%Z = true)) : List (List T) :=
chunk0 T thiss37 s1 thiss37 (Nil_construct T) (Nil_construct (List T)) s1 _.
Fail Next Obligation.


Hint Unfold chunks: definitions.
Program Definition T_type20 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type20.


Program Definition thiss38_type (T: T_type20) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss38_type.


Program Definition i_type (T: T_type20) (thiss38: thiss38_type T) : Type :=
Z.
Fail Next Obligation.


Hint Unfold i_type.


Program Definition drop_rt_type (T: T_type20) (thiss38: thiss38_type T) (i: i_type T thiss38) : Type :=
{res8: List T | (ifthenelse (set_subset (content T res8) (content T thiss38)) bool (fun _ => Zeq_bool (size T res8) (ifthenelse (Z.leb i (0)%Z) Z (fun _ => size T thiss38 ) (fun _ => ifthenelse (Z.geb i (size T thiss38)) Z (fun _ => (0)%Z ) (fun _ => Z.sub (size T thiss38) i ) )) ) (fun _ => false ) = true)}.
Fail Next Obligation.


Hint Unfold drop_rt_type.


Equations drop (T: T_type20) (thiss38: thiss38_type T) (i: i_type T thiss38)  : drop_rt_type T thiss38 i := 
drop T thiss38 i by rec ignore_termination lt :=
drop T thiss38 i := ifthenelse (isNil _ thiss38) (List T) (fun _ => Nil_construct T ) (fun _ => ifthenelse (isCons _ thiss38) (List T) (fun _ => ifthenelse (Z.leb i (0)%Z) (List T) (fun _ => Cons_construct T (h T thiss38) (t3 T thiss38) ) (fun _ => drop T (t3 T thiss38) (Z.sub i (1)%Z) ) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold drop_comp_proj.
Solve Obligations with (repeat t25).
Fail Next Obligation.
Ltac rwrtTac20 := rwrtTac19
  || rewrite drop_equation_1 in *.
Ltac t26 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac20 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t26.
Program Definition T_type21 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type21.


Program Definition thiss39_type (T: T_type21) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss39_type.


Program Definition p7_type (T: T_type21) (thiss39: thiss39_type T) : Type :=
T -> bool.
Fail Next Obligation.


Hint Unfold p7_type.


Program Definition dropWhile_rt_type (T: T_type21) (thiss39: thiss39_type T) (p7: p7_type T thiss39) : Type :=
{res9: List T | (ifthenelse (ifthenelse (Z.leb (size T res9) (size T thiss39)) bool (fun _ => set_subset (content T res9) (content T thiss39) ) (fun _ => false )) bool (fun _ => isEmpty T res9 || negb (p7 (head T res9 _)) ) (fun _ => false ) = true)}.
Fail Next Obligation.


Hint Unfold dropWhile_rt_type.


Equations dropWhile (T: T_type21) (thiss39: thiss39_type T) (p7: p7_type T thiss39)  : dropWhile_rt_type T thiss39 p7 := 
dropWhile T thiss39 p7 by rec ignore_termination lt :=
dropWhile T thiss39 p7 := ifthenelse (ifthenelse (isCons _ thiss39) bool (fun _ => p7 (h T thiss39) ) (fun _ => false )) (List T) (fun _ => dropWhile T (t3 T thiss39) p7 ) (fun _ => thiss39 ).

Hint Unfold dropWhile_comp_proj.
Solve Obligations with (repeat t26).
Fail Next Obligation.
Ltac rwrtTac21 := rwrtTac20
  || rewrite dropWhile_equation_1 in *.
Ltac t27 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac21 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t27.
Program Definition T_type22 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type22.


Program Definition thiss40_type (T: T_type22) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss40_type.


Program Definition p8_type (T: T_type22) (thiss40: thiss40_type T) : Type :=
T -> bool.
Fail Next Obligation.


Hint Unfold p8_type.


Program Definition filter1_rt_type (T: T_type22) (thiss40: thiss40_type T) (p8: p8_type T thiss40) : Type :=
{res10: List T | (ifthenelse (ifthenelse (Z.leb (size T res10) (size T thiss40)) bool (fun _ => set_subset (content T res10) (content T thiss40) ) (fun _ => false )) bool (fun _ => forall1 T res10 p8 ) (fun _ => false ) = true)}.
Fail Next Obligation.


Hint Unfold filter1_rt_type.


Equations filter1 (T: T_type22) (thiss40: thiss40_type T) (p8: p8_type T thiss40)  : filter1_rt_type T thiss40 p8 := 
filter1 T thiss40 p8 by rec ignore_termination lt :=
filter1 T thiss40 p8 := ifthenelse (isNil _ thiss40) (List T) (fun _ => Nil_construct T ) (fun _ => ifthenelse (ifthenelse (isCons _ thiss40) bool (fun _ => p8 (h T thiss40) ) (fun _ => false )) (List T) (fun _ => Cons_construct T (h T thiss40) (filter1 T (t3 T thiss40) p8) ) (fun _ => ifthenelse (isCons _ thiss40) (List T) (fun _ => filter1 T (t3 T thiss40) p8 ) (fun _ => let contradiction: False := _ in match contradiction with end ) ) ).

Hint Unfold filter1_comp_proj.
Solve Obligations with (repeat t27).
Fail Next Obligation.
Ltac rwrtTac22 := rwrtTac21
  || rewrite filter1_equation_1 in *.
Ltac t28 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac22 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t28.
Program Definition T_type23 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type23.


Program Definition thiss41_type (T: T_type23) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss41_type.


Program Definition p9_type (T: T_type23) (thiss41: thiss41_type T) : Type :=
T -> bool.
Fail Next Obligation.


Hint Unfold p9_type.


Program Definition count_rt_type (T: T_type23) (thiss41: thiss41_type T) (p9: p9_type T thiss41) : Type :=
{x___24: Z | (Zeq_bool x___24 (size T (filter1 T thiss41 p9)) = true)}.
Fail Next Obligation.


Hint Unfold count_rt_type.


Equations count (T: T_type23) (thiss41: thiss41_type T) (p9: p9_type T thiss41)  : count_rt_type T thiss41 p9 := 
count T thiss41 p9 by rec ignore_termination lt :=
count T thiss41 p9 := ifthenelse (isNil _ thiss41) Z (fun _ => (0)%Z ) (fun _ => ifthenelse (isCons _ thiss41) Z (fun _ => Z.add (ifthenelse (p9 (h T thiss41)) Z (fun _ => (1)%Z ) (fun _ => (0)%Z )) (count T (t3 T thiss41) p9) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold count_comp_proj.
Solve Obligations with (repeat t28).
Fail Next Obligation.
Ltac rwrtTac23 := rwrtTac22
  || rewrite count_equation_1 in *.
Ltac t29 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac23 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t29.
Program Definition filterNot (T: Type) (thiss42: List T) (p10: T -> bool) : {res11: List T | (ifthenelse (ifthenelse (Z.leb (size T res11) (size T thiss42)) bool (fun _ => set_subset (content T res11) (content T thiss42) ) (fun _ => false )) bool (fun _ => forall1 T res11 (fun x___18 => negb (p10 x___18) ) ) (fun _ => false ) = true)} :=
filter1 T thiss42 (fun x___17 => negb (p10 x___17) ).
Fail Next Obligation.


Hint Unfold filterNot: definitions.
Program Definition T_type24 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type24.


Program Definition ls_type (T: T_type24) : Type :=
List (List T).
Fail Next Obligation.


Hint Unfold ls_type.


Program Definition flatten_rt_type (T: T_type24) (ls: ls_type T) : Type :=
List T.
Fail Next Obligation.


Hint Unfold flatten_rt_type.


Equations flatten (T: T_type24) (ls: ls_type T)  : flatten_rt_type T ls := 
flatten T ls by rec ignore_termination lt :=
flatten T ls := ifthenelse (isCons _ ls) (List T) (fun _ => plus_plus_ T (h (List T) ls) (flatten T (t3 (List T) ls)) ) (fun _ => ifthenelse (isNil _ ls) (List T) (fun _ => Nil_construct T ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold flatten_comp_proj.
Solve Obligations with (repeat t29).
Fail Next Obligation.
Ltac rwrtTac24 := rwrtTac23
  || rewrite flatten_equation_1 in *.
Ltac t30 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac24 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t30.
Program Definition T_type25 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type25.


Program Definition thiss43_type (T: T_type25) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss43_type.


Program Definition contractHyp46_type (T: T_type25) (thiss43: thiss43_type T) : Type :=
(negb (isEmpty T thiss43) = true).
Fail Next Obligation.


Hint Unfold contractHyp46_type.


Program Definition init_rt_type (T: T_type25) (thiss43: thiss43_type T) (contractHyp46: contractHyp46_type T thiss43) : Type :=
{r: List T | (ifthenelse (Zeq_bool (size T r) (Z.sub (size T thiss43) (1)%Z)) bool (fun _ => set_subset (content T r) (content T thiss43) ) (fun _ => false ) = true)}.
Fail Next Obligation.


Hint Unfold init_rt_type.


Equations init (T: T_type25) (thiss43: thiss43_type T) (contractHyp46: contractHyp46_type T thiss43)  : init_rt_type T thiss43 contractHyp46 := 
init T thiss43 contractHyp46 by rec ignore_termination lt :=
init T thiss43 contractHyp46 := ifthenelse (ifthenelse (isCons _ thiss43) bool (fun _ => isNil _ (t3 T thiss43) ) (fun _ => false )) (List T) (fun _ => Nil_construct T ) (fun _ => ifthenelse (isCons _ thiss43) (List T) (fun _ => Cons_construct T (h T thiss43) (init T (t3 T thiss43) _) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold init_comp_proj.
Solve Obligations with (repeat t30).
Fail Next Obligation.
Ltac rwrtTac25 := rwrtTac24
  || rewrite init_equation_1 in *.
Ltac t31 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac25 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t31.
Program Definition T_type26 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type26.


Program Definition thiss44_type (T: T_type26) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss44_type.


Program Definition pos_type (T: T_type26) (thiss44: thiss44_type T) : Type :=
Z.
Fail Next Obligation.


Hint Unfold pos_type.


Program Definition l1_type (T: T_type26) (thiss44: thiss44_type T) (pos: pos_type T thiss44) : Type :=
List T.
Fail Next Obligation.


Hint Unfold l1_type.


Program Definition contractHyp47_type (T: T_type26) (thiss44: thiss44_type T) (pos: pos_type T thiss44) (l1: l1_type T thiss44 pos) : Type :=
(ifthenelse (Z.leb (0)%Z pos) bool (fun _ => Z.leb pos (size T thiss44) ) (fun _ => false ) = true).
Fail Next Obligation.


Hint Unfold contractHyp47_type.


Program Definition insertAtImpl_rt_type (T: T_type26) (thiss44: thiss44_type T) (pos: pos_type T thiss44) (l1: l1_type T thiss44 pos) (contractHyp47: contractHyp47_type T thiss44 pos l1) : Type :=
{res12: List T | (ifthenelse (Zeq_bool (size T res12) (Z.add (size T thiss44) (size T l1))) bool (fun _ => set_equality (content T res12) (set_union (content T thiss44) (content T l1)) ) (fun _ => false ) = true)}.
Fail Next Obligation.


Hint Unfold insertAtImpl_rt_type.


Equations insertAtImpl (T: T_type26) (thiss44: thiss44_type T) (pos: pos_type T thiss44) (l1: l1_type T thiss44 pos) (contractHyp47: contractHyp47_type T thiss44 pos l1)  : insertAtImpl_rt_type T thiss44 pos l1 contractHyp47 := 
insertAtImpl T thiss44 pos l1 contractHyp47 by rec ignore_termination lt :=
insertAtImpl T thiss44 pos l1 contractHyp47 := ifthenelse (Zeq_bool pos (0)%Z) (List T) (fun _ => plus_plus_ T l1 thiss44 ) (fun _ => ifthenelse (isCons _ thiss44) (List T) (fun _ => Cons_construct T (h T thiss44) (insertAtImpl T (t3 T thiss44) (Z.sub pos (1)%Z) l1 _) ) (fun _ => ifthenelse (isNil _ thiss44) (List T) (fun _ => l1 ) (fun _ => let contradiction: False := _ in match contradiction with end ) ) ).

Hint Unfold insertAtImpl_comp_proj.
Solve Obligations with (repeat t31).
Fail Next Obligation.
Ltac rwrtTac26 := rwrtTac25
  || rewrite insertAtImpl_equation_1 in *.
Ltac t32 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac26 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t32.
Program Definition insertAt (T: Type) (thiss45: List T) (pos1: Z) (l2: List T) (contractHyp48: (ifthenelse (Z.leb (Z.opp pos1) (size T thiss45)) bool (fun _ => Z.leb pos1 (size T thiss45) ) (fun _ => false ) = true)) : {res13: List T | (ifthenelse (Zeq_bool (size T res13) (Z.add (size T thiss45) (size T l2))) bool (fun _ => set_equality (content T res13) (set_union (content T thiss45) (content T l2)) ) (fun _ => false ) = true)} :=
ifthenelse (Z.ltb pos1 (0)%Z) (List T) (fun _ => insertAtImpl T thiss45 (Z.add (size T thiss45) pos1) l2 _ ) (fun _ => insertAtImpl T thiss45 pos1 l2 _ ).
Fail Next Obligation.


Hint Unfold insertAt: definitions.
Program Definition insertAt1 (T: Type) (thiss46: List T) (pos2: Z) (e1: T) (contractHyp49: (ifthenelse (Z.leb (Z.opp pos2) (size T thiss46)) bool (fun _ => Z.leb pos2 (size T thiss46) ) (fun _ => false ) = true)) : {res14: List T | (ifthenelse (Zeq_bool (size T res14) (Z.add (size T thiss46) (1)%Z)) bool (fun _ => set_equality (content T res14) (set_union (content T thiss46) (set_union (@set_empty T) (set_singleton e1))) ) (fun _ => false ) = true)} :=
insertAt T thiss46 pos2 (Cons_construct T e1 (Nil_construct T)) _.
Fail Next Obligation.


Hint Unfold insertAt1: definitions.
Program Definition length (T: Type) (thiss47: List T) : Z :=
size T thiss47.
Fail Next Obligation.


Hint Unfold length: definitions.
Program Definition T_type27 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type27.


Program Definition R_type5 (T: T_type27) : Type :=
Type.
Fail Next Obligation.


Hint Unfold R_type5.


Program Definition thiss48_type (T: T_type27) (R: R_type5 T) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss48_type.


Program Definition f7_type (T: T_type27) (R: R_type5 T) (thiss48: thiss48_type T R) : Type :=
T -> R.
Fail Next Obligation.


Hint Unfold f7_type.


Program Definition map1_rt_type (T: T_type27) (R: R_type5 T) (thiss48: thiss48_type T R) (f7: f7_type T R thiss48) : Type :=
{x___9: List R | (Zeq_bool (size R x___9) (size T thiss48) = true)}.
Fail Next Obligation.


Hint Unfold map1_rt_type.


Equations map1 (T: T_type27) (R: R_type5 T) (thiss48: thiss48_type T R) (f7: f7_type T R thiss48)  : map1_rt_type T R thiss48 f7 := 
map1 T R thiss48 f7 by rec ignore_termination lt :=
map1 T R thiss48 f7 := ifthenelse (isNil _ thiss48) (List R) (fun _ => Nil_construct R ) (fun _ => ifthenelse (isCons _ thiss48) (List R) (fun _ => let x___8 := (f7 (h T thiss48)) in (cons_ R (map1 T R (t3 T thiss48) f7) x___8) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold map1_comp_proj.
Solve Obligations with (repeat t32).
Fail Next Obligation.
Ltac rwrtTac27 := rwrtTac26
  || rewrite map1_equation_1 in *.
Ltac t33 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac27 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t33.
Program Definition flatMap1 (T: Type) (R: Type) (thiss49: List T) (f8: T -> (List R)) : List R :=
flatten R (map1 T (List R) thiss49 f8).
Fail Next Obligation.


Hint Unfold flatMap1: definitions.
Program Definition T_type28 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type28.


Program Definition thiss50_type (T: T_type28) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss50_type.


Program Definition s2_type (T: T_type28) (thiss50: thiss50_type T) : Type :=
Z.
Fail Next Obligation.


Hint Unfold s2_type.


Program Definition e2_type (T: T_type28) (thiss50: thiss50_type T) (s2: s2_type T thiss50) : Type :=
T.
Fail Next Obligation.


Hint Unfold e2_type.


Program Definition padTo_rt_type (T: T_type28) (thiss50: thiss50_type T) (s2: s2_type T thiss50) (e2: e2_type T thiss50 s2) : Type :=
{res15: List T | (ifthenelse (Z.leb s2 (size T thiss50)) bool (fun _ => propInBool ((res15 = thiss50)) ) (fun _ => ifthenelse (Zeq_bool (size T res15) s2) bool (fun _ => set_equality (content T res15) (set_union (content T thiss50) (set_union (@set_empty T) (set_singleton e2))) ) (fun _ => false ) ) = true)}.
Fail Next Obligation.


Hint Unfold padTo_rt_type.


Equations padTo (T: T_type28) (thiss50: thiss50_type T) (s2: s2_type T thiss50) (e2: e2_type T thiss50 s2)  : padTo_rt_type T thiss50 s2 e2 := 
padTo T thiss50 s2 e2 by rec ignore_termination lt :=
padTo T thiss50 s2 e2 := ifthenelse (Z.leb s2 (0)%Z) (List T) (fun _ => thiss50 ) (fun _ => ifthenelse (isNil _ thiss50) (List T) (fun _ => Cons_construct T e2 (padTo T (Nil_construct T) (Z.sub s2 (1)%Z) e2) ) (fun _ => ifthenelse (isCons _ thiss50) (List T) (fun _ => Cons_construct T (h T thiss50) (padTo T (t3 T thiss50) (Z.sub s2 (1)%Z) e2) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ) ).

Hint Unfold padTo_comp_proj.
Solve Obligations with (repeat t33).
Fail Next Obligation.
Ltac rwrtTac28 := rwrtTac27
  || rewrite padTo_equation_1 in *.
Ltac t34 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac28 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t34.
Program Definition T_type29 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type29.


Program Definition thiss51_type (T: T_type29) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss51_type.


Program Definition p11_type (T: T_type29) (thiss51: thiss51_type T) : Type :=
T -> bool.
Fail Next Obligation.


Hint Unfold p11_type.


Program Definition partition_rt_type (T: T_type29) (thiss51: thiss51_type T) (p11: p11_type T thiss51) : Type :=
{res16: ((List T) * (List T))%type | (ifthenelse (propInBool ((fst res16 = filter1 T thiss51 p11))) bool (fun _ => propInBool ((snd res16 = filterNot T thiss51 p11)) ) (fun _ => false ) = true)}.
Fail Next Obligation.


Hint Unfold partition_rt_type.


Equations partition (T: T_type29) (thiss51: thiss51_type T) (p11: p11_type T thiss51)  : partition_rt_type T thiss51 p11 := 
partition T thiss51 p11 by rec ignore_termination lt :=
partition T thiss51 p11 := ifthenelse (isNil _ thiss51) (((List T) * (List T))%type) (fun _ => (Nil_construct T,Nil_construct T) ) (fun _ => ifthenelse (isCons _ thiss51) (((List T) * (List T))%type) (fun _ => let x___19 := ((fst (partition T (t3 T thiss51) p11),snd (partition T (t3 T thiss51) p11))) in (let l2 := (snd x___19) in (ifthenelse (p11 (h T thiss51)) (((List T) * (List T))%type) (fun _ => (cons_ T (fst x___19) (h T thiss51),l2) ) (fun _ => (fst x___19,cons_ T l2 (h T thiss51)) ))) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold partition_comp_proj.
Solve Obligations with (repeat t34).
Fail Next Obligation.
Ltac rwrtTac29 := rwrtTac28
  || rewrite partition_equation_1 in *.
Ltac t35 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac29 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t35.
Program Definition T_type30 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type30.


Program Definition thiss52_type (T: T_type30) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss52_type.


Program Definition from_type (T: T_type30) (thiss52: thiss52_type T) (from: from_type T thiss52 from) : Type :=
T.
Fail Next Obligation.


Hint Unfold from_type.


Program Definition from_type (T: T_type30) (thiss52: thiss52_type T) (from: from_type T thiss52 from) : Type :=
T.
Fail Next Obligation.


Hint Unfold from_type.


Program Definition replace_rt_type (T: T_type30) (thiss52: thiss52_type T) (from: from_type T thiss52 from) (to: from_type T thiss52 from) : Type :=
{res17: List T | (ifthenelse (Zeq_bool (size T res17) (size T thiss52)) bool (fun _ => set_equality (content T res17) (set_union (set_difference (content T thiss52) (set_union (@set_empty T) (set_singleton from))) (ifthenelse (set_elem_of from (content T thiss52)) (set (T)) (fun _ => set_union (@set_empty T) (set_singleton to) ) (fun _ => @set_empty T ))) ) (fun _ => false ) = true)}.
Fail Next Obligation.


Hint Unfold replace_rt_type.


Equations replace (T: T_type30) (thiss52: thiss52_type T) (from: from_type T thiss52 from) (to: from_type T thiss52 from)  : replace_rt_type T thiss52 from to := 
replace T thiss52 from to by rec ignore_termination lt :=
replace T thiss52 from to := ifthenelse (isNil _ thiss52) (List T) (fun _ => Nil_construct T ) (fun _ => ifthenelse (isCons _ thiss52) (List T) (fun _ => let r1 := (replace T (t3 T thiss52) from to) in (ifthenelse (propInBool ((h T thiss52 = from))) (List T) (fun _ => Cons_construct T to r1 ) (fun _ => Cons_construct T (h T thiss52) r1 )) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold replace_comp_proj.
Solve Obligations with (repeat t35).
Fail Next Obligation.
Ltac rwrtTac30 := rwrtTac29
  || rewrite replace_equation_1 in *.
Ltac t36 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac30 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t36.
Program Definition T_type31 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type31.


Program Definition thiss53_type (T: T_type31) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss53_type.


Program Definition pos3_type (T: T_type31) (thiss53: thiss53_type T) (pos3: pos3_type T thiss53 pos3) : Type :=
Z.
Fail Next Obligation.


Hint Unfold pos3_type.


Program Definition pos3_type (T: T_type31) (thiss53: thiss53_type T) (pos3: pos3_type T thiss53 pos3) : Type :=
List T.
Fail Next Obligation.


Hint Unfold pos3_type.


Program Definition contractHyp56_type (T: T_type31) (thiss53: thiss53_type T) (pos3: pos3_type T thiss53 pos3) (l3: pos3_type T thiss53 pos3) : Type :=
(ifthenelse (Z.leb (0)%Z pos3) bool (fun _ => Z.leb pos3 (size T thiss53) ) (fun _ => false ) = true).
Fail Next Obligation.


Hint Unfold contractHyp56_type.


Program Definition replaceAtImpl_rt_type (T: T_type31) (thiss53: thiss53_type T) (pos3: pos3_type T thiss53 pos3) (l3: pos3_type T thiss53 pos3) (contractHyp56: contractHyp56_type T thiss53 pos3 l3) : Type :=
{res18: List T | (set_subset (content T res18) (set_union (content T l3) (content T thiss53)) = true)}.
Fail Next Obligation.


Hint Unfold replaceAtImpl_rt_type.


Equations replaceAtImpl (T: T_type31) (thiss53: thiss53_type T) (pos3: pos3_type T thiss53 pos3) (l3: pos3_type T thiss53 pos3) (contractHyp56: contractHyp56_type T thiss53 pos3 l3)  : replaceAtImpl_rt_type T thiss53 pos3 l3 contractHyp56 := 
replaceAtImpl T thiss53 pos3 l3 contractHyp56 by rec ignore_termination lt :=
replaceAtImpl T thiss53 pos3 l3 contractHyp56 := ifthenelse (Zeq_bool pos3 (0)%Z) (List T) (fun _ => plus_plus_ T l3 (drop T thiss53 (size T l3)) ) (fun _ => ifthenelse (isCons _ thiss53) (List T) (fun _ => Cons_construct T (h T thiss53) (replaceAtImpl T (t3 T thiss53) (Z.sub pos3 (1)%Z) l3 _) ) (fun _ => ifthenelse (isNil _ thiss53) (List T) (fun _ => l3 ) (fun _ => let contradiction: False := _ in match contradiction with end ) ) ).

Hint Unfold replaceAtImpl_comp_proj.
Solve Obligations with (repeat t36).
Fail Next Obligation.
Ltac rwrtTac31 := rwrtTac30
  || rewrite replaceAtImpl_equation_1 in *.
Ltac t37 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac31 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t37.
Program Definition replaceAt (T: Type) (thiss54: List T) (pos4: Z) (l4: List T) (contractHyp57: (ifthenelse (Z.leb (Z.opp pos4) (size T thiss54)) bool (fun _ => Z.leb pos4 (size T thiss54) ) (fun _ => false ) = true)) : {res19: List T | (set_subset (content T res19) (set_union (content T l4) (content T thiss54)) = true)} :=
ifthenelse (Z.ltb pos4 (0)%Z) (List T) (fun _ => replaceAtImpl T thiss54 (Z.add (size T thiss54) pos4) l4 _ ) (fun _ => replaceAtImpl T thiss54 pos4 l4 _ ).
Fail Next Obligation.


Hint Unfold replaceAt: definitions.
Program Definition T_type32 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type32.


Program Definition thiss55_type (T: T_type32) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss55_type.


Program Definition reverse_rt_type (T: T_type32) (thiss55: thiss55_type T) : Type :=
{res20: List T | (ifthenelse (Zeq_bool (size T res20) (size T thiss55)) bool (fun _ => set_equality (content T res20) (content T thiss55) ) (fun _ => false ) = true)}.
Fail Next Obligation.


Hint Unfold reverse_rt_type.


Equations reverse (T: T_type32) (thiss55: thiss55_type T)  : reverse_rt_type T thiss55 := 
reverse T thiss55 by rec ignore_termination lt :=
reverse T thiss55 := ifthenelse (isNil _ thiss55) (List T) (fun _ => thiss55 ) (fun _ => ifthenelse (isCons _ thiss55) (List T) (fun _ => snoc_ T (reverse T (t3 T thiss55)) (h T thiss55) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold reverse_comp_proj.
Solve Obligations with (repeat t37).
Fail Next Obligation.
Ltac rwrtTac32 := rwrtTac31
  || rewrite reverse_equation_1 in *.
Ltac t38 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac32 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t38.
Program Definition tail (T: Type) (thiss56: List T) (contractHyp59: (negb (propInBool ((thiss56 = Nil_construct T))) = true)) : List T :=
ifthenelse (isCons _ thiss56) (List T) (fun _ => t3 T thiss56 ) (fun _ => let contradiction: False := _ in match contradiction with end ).
Fail Next Obligation.


Hint Unfold tail: definitions.
Program Definition T_type33 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type33.


Program Definition thiss57_type (T: T_type33) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss57_type.


Program Definition index_type (T: T_type33) (thiss57: thiss57_type T) : Type :=
Z.
Fail Next Obligation.


Hint Unfold index_type.


Program Definition contractHyp60_type (T: T_type33) (thiss57: thiss57_type T) (index: index_type T thiss57) : Type :=
(ifthenelse (Z.leb (0)%Z index) bool (fun _ => Z.ltb index (size T thiss57) ) (fun _ => false ) = true).
Fail Next Obligation.


Hint Unfold contractHyp60_type.


Program Definition apply_rt_type (T: T_type33) (thiss57: thiss57_type T) (index: index_type T thiss57) (contractHyp60: contractHyp60_type T thiss57 index) : Type :=
T.
Fail Next Obligation.


Hint Unfold apply_rt_type.


Equations apply (T: T_type33) (thiss57: thiss57_type T) (index: index_type T thiss57) (contractHyp60: contractHyp60_type T thiss57 index)  : apply_rt_type T thiss57 index contractHyp60 := 
apply T thiss57 index contractHyp60 by rec ignore_termination lt :=
apply T thiss57 index contractHyp60 := ifthenelse (Zeq_bool index (0)%Z) T (fun _ => head T thiss57 _ ) (fun _ => apply T (tail T thiss57 _) (Z.sub index (1)%Z) _ ).

Hint Unfold apply_comp_proj.
Solve Obligations with (repeat t38).
Fail Next Obligation.
Ltac rwrtTac33 := rwrtTac32
  || rewrite apply_equation_1 in *.
Ltac t39 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac33 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t39.
Program Definition T_type34 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type34.


Program Definition thiss58_type (T: T_type34) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss58_type.


Program Definition seps_type (T: T_type34) (thiss58: thiss58_type T) : Type :=
List T.
Fail Next Obligation.


Hint Unfold seps_type.


Program Definition split_rt_type (T: T_type34) (thiss58: thiss58_type T) (seps: seps_type T thiss58) : Type :=
List (List T).
Fail Next Obligation.


Hint Unfold split_rt_type.


Equations split (T: T_type34) (thiss58: thiss58_type T) (seps: seps_type T thiss58)  : split_rt_type T thiss58 seps := 
split T thiss58 seps by rec ignore_termination lt :=
split T thiss58 seps := ifthenelse (isCons _ thiss58) (List (List T)) (fun _ => ifthenelse (contains T seps (h T thiss58)) (List (List T)) (fun _ => Cons_construct (List T) (Nil_construct T) (split T (t3 T thiss58) seps) ) (fun _ => let r2 := (split T (t3 T thiss58) seps) in (Cons_construct (List T) (Cons_construct T (h T thiss58) (head (List T) r2 _)) (tail (List T) r2 _)) ) ) (fun _ => ifthenelse (isNil _ thiss58) (List (List T)) (fun _ => Cons_construct (List T) (Nil_construct T) (Nil_construct (List T)) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold split_comp_proj.
Solve Obligations with (repeat t39).
Fail Next Obligation.
Ltac rwrtTac34 := rwrtTac33
  || rewrite split_equation_1 in *.
Ltac t40 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac34 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t40.
Program Definition splitAt (T: Type) (thiss59: List T) (e3: T) : List (List T) :=
split T thiss59 (Cons_construct T e3 (Nil_construct T)).
Fail Next Obligation.


Hint Unfold splitAt: definitions.
Program Definition tailOption (T: Type) (thiss60: List T) : {x___6: Option (List T) | (negb (Bool.eqb (isDefined (List T) x___6) (isEmpty T thiss60)) = true)} :=
ifthenelse (isCons _ thiss60) (Option (List T)) (fun _ => Some_construct (List T) (t3 T thiss60) ) (fun _ => ifthenelse (isNil _ thiss60) (Option (List T)) (fun _ => None_construct (List T) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).
Fail Next Obligation.


Hint Unfold tailOption: definitions.
Program Definition T_type35 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type35.


Program Definition l5_type (T: T_type35) : Type :=
List T.
Fail Next Obligation.


Hint Unfold l5_type.


Program Definition tails_rt_type (T: T_type35) (l5: l5_type T) : Type :=
List (List T).
Fail Next Obligation.


Hint Unfold tails_rt_type.


Equations tails (T: T_type35) (l5: l5_type T)  : tails_rt_type T l5 := 
tails T l5 by rec ignore_termination lt :=
tails T l5 := ifthenelse (isCons _ l5) (List (List T)) (fun _ => Cons_construct (List T) (t3 T l5) (tails T (t3 T l5)) ) (fun _ => ifthenelse (isNil _ l5) (List (List T)) (fun _ => Cons_construct (List T) (Nil_construct T) (Nil_construct (List T)) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold tails_comp_proj.
Solve Obligations with (repeat t40).
Fail Next Obligation.
Ltac rwrtTac35 := rwrtTac34
  || rewrite tails_equation_1 in *.
Ltac t41 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac35 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t41.
Program Definition T_type36 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type36.


Program Definition thiss61_type (T: T_type36) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss61_type.


Program Definition i1_type (T: T_type36) (thiss61: thiss61_type T) : Type :=
Z.
Fail Next Obligation.


Hint Unfold i1_type.


Program Definition take_rt_type (T: T_type36) (thiss61: thiss61_type T) (i1: i1_type T thiss61) : Type :=
{res21: List T | (ifthenelse (set_subset (content T res21) (content T thiss61)) bool (fun _ => Zeq_bool (size T res21) (ifthenelse (Z.leb i1 (0)%Z) Z (fun _ => (0)%Z ) (fun _ => ifthenelse (Z.geb i1 (size T thiss61)) Z (fun _ => size T thiss61 ) (fun _ => i1 ) )) ) (fun _ => false ) = true)}.
Fail Next Obligation.


Hint Unfold take_rt_type.


Equations take (T: T_type36) (thiss61: thiss61_type T) (i1: i1_type T thiss61)  : take_rt_type T thiss61 i1 := 
take T thiss61 i1 by rec ignore_termination lt :=
take T thiss61 i1 := ifthenelse (isNil _ thiss61) (List T) (fun _ => Nil_construct T ) (fun _ => ifthenelse (isCons _ thiss61) (List T) (fun _ => ifthenelse (Z.leb i1 (0)%Z) (List T) (fun _ => Nil_construct T ) (fun _ => Cons_construct T (h T thiss61) (take T (t3 T thiss61) (Z.sub i1 (1)%Z)) ) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold take_comp_proj.
Solve Obligations with (repeat t41).
Fail Next Obligation.
Ltac rwrtTac36 := rwrtTac35
  || rewrite take_equation_1 in *.
Ltac t42 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac36 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t42.
Program Definition evenSplit (T: Type) (thiss62: List T) : ((List T) * (List T))%type :=
let c := (Z.div (size T thiss62) (2)%Z) in ((take T thiss62 c,drop T thiss62 c)).
Fail Next Obligation.


Hint Unfold evenSplit: definitions.
Program Definition rotate (T: Type) (thiss63: List T) (s3: Z) : {res22: List T | (Zeq_bool (size T res22) (size T thiss63) = true)} :=
ifthenelse (isEmpty T thiss63) (List T) (fun _ => Nil_construct T ) (fun _ => plus_plus_ T (drop T thiss63 (Z.modulo s3 (size T thiss63))) (take T thiss63 (Z.modulo s3 (size T thiss63))) ).
Fail Next Obligation.


Hint Unfold rotate: definitions.
Program Definition slice (T: Type) (thiss64: List T) (from1: Z) (to1: Z) (contractHyp68: (ifthenelse (ifthenelse (Z.leb (0)%Z from1) bool (fun _ => Z.leb from1 to1 ) (fun _ => false )) bool (fun _ => Z.leb to1 (size T thiss64) ) (fun _ => false ) = true)) : List T :=
take T (drop T thiss64 from1) (Z.sub to1 from1).
Fail Next Obligation.


Hint Unfold slice: definitions.
Program Definition T_type37 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type37.


Program Definition thiss65_type (T: T_type37) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss65_type.


Program Definition index1_type (T: T_type37) (thiss65: thiss65_type T) : Type :=
Z.
Fail Next Obligation.


Hint Unfold index1_type.


Program Definition splitAtIndex_rt_type (T: T_type37) (thiss65: thiss65_type T) (index1: index1_type T thiss65) : Type :=
{res23: ((List T) * (List T))%type | (ifthenelse (ifthenelse (propInBool ((plus_plus_ T (fst res23) (snd res23) = thiss65))) bool (fun _ => propInBool ((fst res23 = take T thiss65 index1)) ) (fun _ => false )) bool (fun _ => propInBool ((snd res23 = drop T thiss65 index1)) ) (fun _ => false ) = true)}.
Fail Next Obligation.


Hint Unfold splitAtIndex_rt_type.


Equations splitAtIndex (T: T_type37) (thiss65: thiss65_type T) (index1: index1_type T thiss65)  : splitAtIndex_rt_type T thiss65 index1 := 
splitAtIndex T thiss65 index1 by rec ignore_termination lt :=
splitAtIndex T thiss65 index1 := ifthenelse (isNil _ thiss65) (((List T) * (List T))%type) (fun _ => (Nil_construct T,Nil_construct T) ) (fun _ => ifthenelse (isCons _ thiss65) (((List T) * (List T))%type) (fun _ => ifthenelse (Z.leb index1 (0)%Z) (((List T) * (List T))%type) (fun _ => (Nil_construct T,thiss65) ) (fun _ => let x___7 := ((fst (splitAtIndex T (t3 T thiss65) (Z.sub index1 (1)%Z)),snd (splitAtIndex T (t3 T thiss65) (Z.sub index1 (1)%Z)))) in (let right := (snd x___7) in ((Cons_construct T (h T thiss65) (fst x___7),right))) ) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold splitAtIndex_comp_proj.
Solve Obligations with (repeat t42).
Fail Next Obligation.
Ltac rwrtTac37 := rwrtTac36
  || rewrite splitAtIndex_equation_1 in *.
Ltac t43 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac37 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t43.
Program Definition T_type38 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type38.


Program Definition thiss66_type (T: T_type38) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss66_type.


Program Definition p12_type (T: T_type38) (thiss66: thiss66_type T) : Type :=
T -> bool.
Fail Next Obligation.


Hint Unfold p12_type.


Program Definition takeWhile_rt_type (T: T_type38) (thiss66: thiss66_type T) (p12: p12_type T thiss66) : Type :=
{res24: List T | (ifthenelse (ifthenelse (forall1 T res24 p12) bool (fun _ => Z.leb (size T res24) (size T thiss66) ) (fun _ => false )) bool (fun _ => set_subset (content T res24) (content T thiss66) ) (fun _ => false ) = true)}.
Fail Next Obligation.


Hint Unfold takeWhile_rt_type.


Equations takeWhile (T: T_type38) (thiss66: thiss66_type T) (p12: p12_type T thiss66)  : takeWhile_rt_type T thiss66 p12 := 
takeWhile T thiss66 p12 by rec ignore_termination lt :=
takeWhile T thiss66 p12 := ifthenelse (ifthenelse (isCons _ thiss66) bool (fun _ => p12 (h T thiss66) ) (fun _ => false )) (List T) (fun _ => Cons_construct T (h T thiss66) (takeWhile T (t3 T thiss66) p12) ) (fun _ => Nil_construct T ).

Hint Unfold takeWhile_comp_proj.
Solve Obligations with (repeat t43).
Fail Next Obligation.
Ltac rwrtTac38 := rwrtTac37
  || rewrite takeWhile_equation_1 in *.
Ltac t44 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac38 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t44.
Program Definition toSet (T: Type) (thiss67: List T) : set (T) :=
foldLeft T (set (T)) thiss67 (@set_empty T) (fun x0___1 => fun x1___1 => set_union x0___1 (set_union (@set_empty T) (set_singleton x1___1))  ).
Fail Next Obligation.


Hint Unfold toSet: definitions.
Program Definition toSet1 (T: Type) (thiss68: Option T) : set (T) :=
ifthenelse (isNone _ thiss68) (set (T)) (fun _ => @set_empty T ) (fun _ => ifthenelse (isSome _ thiss68) (set (T)) (fun _ => set_union (@set_empty T) (set_singleton (v T thiss68)) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).
Fail Next Obligation.


Hint Unfold toSet1: definitions.
Program Definition T_type39 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type39.


Program Definition thiss69_type (T: T_type39) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss69_type.


Program Definition unique_rt_type (T: T_type39) (thiss69: thiss69_type T) : Type :=
List T.
Fail Next Obligation.


Hint Unfold unique_rt_type.


Equations unique (T: T_type39) (thiss69: thiss69_type T)  : unique_rt_type T thiss69 := 
unique T thiss69 by rec ignore_termination lt :=
unique T thiss69 := ifthenelse (isNil _ thiss69) (List T) (fun _ => Nil_construct T ) (fun _ => ifthenelse (isCons _ thiss69) (List T) (fun _ => Cons_construct T (h T thiss69) (minus_ T (unique T (t3 T thiss69)) (h T thiss69)) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold unique_comp_proj.
Solve Obligations with (repeat t44).
Fail Next Obligation.
Ltac rwrtTac39 := rwrtTac38
  || rewrite unique_equation_1 in *.
Ltac t45 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac39 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t45.
Program Definition T_type40 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type40.


Program Definition thiss70_type (T: T_type40) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss70_type.


Program Definition i2_type (T: T_type40) (thiss70: thiss70_type T) : Type :=
Z.
Fail Next Obligation.


Hint Unfold i2_type.


Program Definition y_type (T: T_type40) (thiss70: thiss70_type T) (i2: i2_type T thiss70) : Type :=
T.
Fail Next Obligation.


Hint Unfold y_type.


Program Definition contractHyp74_type (T: T_type40) (thiss70: thiss70_type T) (i2: i2_type T thiss70) (y: y_type T thiss70 i2) : Type :=
(ifthenelse (Z.leb (0)%Z i2) bool (fun _ => Z.ltb i2 (size T thiss70) ) (fun _ => false ) = true).
Fail Next Obligation.


Hint Unfold contractHyp74_type.


Program Definition updated_rt_type (T: T_type40) (thiss70: thiss70_type T) (i2: i2_type T thiss70) (y: y_type T thiss70 i2) (contractHyp74: contractHyp74_type T thiss70 i2 y) : Type :=
List T.
Fail Next Obligation.


Hint Unfold updated_rt_type.


Equations updated (T: T_type40) (thiss70: thiss70_type T) (i2: i2_type T thiss70) (y: y_type T thiss70 i2) (contractHyp74: contractHyp74_type T thiss70 i2 y)  : updated_rt_type T thiss70 i2 y contractHyp74 := 
updated T thiss70 i2 y contractHyp74 by rec ignore_termination lt :=
updated T thiss70 i2 y contractHyp74 := ifthenelse (ifthenelse (isCons _ thiss70) bool (fun _ => Zeq_bool i2 (0)%Z ) (fun _ => false )) (List T) (fun _ => Cons_construct T y (t3 T thiss70) ) (fun _ => ifthenelse (isCons _ thiss70) (List T) (fun _ => Cons_construct T (h T thiss70) (updated T (t3 T thiss70) (Z.sub i2 (1)%Z) y _) ) (fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold updated_comp_proj.
Solve Obligations with (repeat t45).
Fail Next Obligation.
Ltac rwrtTac40 := rwrtTac39
  || rewrite updated_equation_1 in *.
Ltac t46 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac40 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t46.
Program Definition withFilter (T: Type) (thiss71: List T) (p13: T -> bool) : List T :=
filter1 T thiss71 p13.
Fail Next Obligation.


Hint Unfold withFilter: definitions.
Program Definition withFilter1 (T: Type) (thiss72: Option T) (p14: T -> bool) : Option T :=
filter T thiss72 p14.
Fail Next Obligation.


Hint Unfold withFilter1: definitions.
Program Definition T_type41 : Type :=
Type.
Fail Next Obligation.


Hint Unfold T_type41.


Program Definition B_type (T: T_type41) : Type :=
Type.
Fail Next Obligation.


Hint Unfold B_type.


Program Definition thiss73_type (T: T_type41) (B: B_type T) : Type :=
List T.
Fail Next Obligation.


Hint Unfold thiss73_type.


Program Definition that3_type (T: T_type41) (B: B_type T) (thiss73: thiss73_type T B) : Type :=
List B.
Fail Next Obligation.


Hint Unfold that3_type.


Program Definition zip_rt_type (T: T_type41) (B: B_type T) (thiss73: thiss73_type T B) (that3: that3_type T B thiss73) : Type :=
{x___31: List ((T * B)%type) | (Zeq_bool (size ((T * B)%type) x___31) (ifthenelse (Z.leb (size T thiss73) (size B that3)) Z (fun _ => size T thiss73 ) (fun _ => size B that3 )) = true)}.
Fail Next Obligation.


Hint Unfold zip_rt_type.


Equations zip (T: T_type41) (B: B_type T) (thiss73: thiss73_type T B) (that3: that3_type T B thiss73)  : zip_rt_type T B thiss73 that3 := 
zip T B thiss73 that3 by rec ignore_termination lt :=
zip T B thiss73 that3 := ifthenelse (ifthenelse (isCons _ thiss73) bool (fun _ => isCons _ that3 ) (fun _ => false )) (List ((T * B)%type)) (fun _ => Cons_construct ((T * B)%type) ((h T thiss73,h B that3)) (zip T B (t3 T thiss73) (t3 B that3)) ) (fun _ => Nil_construct ((T * B)%type) ).

Hint Unfold zip_comp_proj.
Solve Obligations with (repeat t46).
Fail Next Obligation.
Ltac rwrtTac41 := rwrtTac40
  || rewrite zip_equation_1 in *.
Ltac t47 := 
  t ||
  List_tactic ||
  t_sets ||
  rwrtTac41 ||
  autounfold with recognizers in * ||
  rewrite propInBool in *.
Obligation Tactic := repeat t47.
