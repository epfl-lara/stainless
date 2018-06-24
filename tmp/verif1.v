Require Import SLC.Lib.
Require Import SLC.PropBool.
Require Import SLC.Booleans.
Require Import stdpp.set.
Require Import SLC.stdppSets.
Require Import SLC.Tactics.
Require Import SLC.Ints.
Set Program Mode.
Ltac t426 :=
  t_base ||
  List_tactic76 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac164 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t426.


Inductive Option (T: Type) :=
| None_construct: Option T
| Some_construct: T -> (Option T).

Definition isNone (T: Type) (src: Option T) : bool :=
match src with
| None_construct _ => true
| _ => false
end.

Fail Next Obligation.

Hint Unfold  isNone: recognizers. 

Definition isSome (T: Type) (src: Option T) : bool :=
match src with
| Some_construct _ _ => true
| _ => false
end.

Fail Next Obligation.

Hint Unfold  isSome: recognizers. 

Lemma None_exists: (forall T: Type, forall self616: Option T, ((true = isNone T self616)) <-> (((None_construct T = self616)))). 
Proof.
	repeat t426 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self617: Option T, ((true = isSome T self617)) <-> ((exists tmp231: T, (Some_construct T tmp231 = self617)))). 
Proof.
	repeat t426 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic77 := match goal with 
	| [ H308: (true = isNone ?T ?self618) |- _ ] => 
			poseNew (Mark (T,self618) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H308)
	| [ H308: (isNone ?T ?self618 = true) |- _ ] => 
			poseNew (Mark (T,self618) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H308))
	| [ H309: (true = isSome ?T ?self619) |- _ ] => 
			poseNew (Mark (T,self619) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H309)
	| [ H309: (isSome ?T ?self619 = true) |- _ ] => 
			poseNew (Mark (T,self619) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H309))
	| _ => List_tactic76
end.

Ltac t427 :=
  t_base ||
  Option_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac164 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t427.


Definition v (T: Type) (src: Some_type T) : T :=
match src with
| Some_construct _ f0 => f0
| _ => let contradiction: False := _ in match contradiction with end
end.

Fail Next Obligation.

Inductive List (T: Type) :=
| Cons_construct: T -> ((List T) -> (List T))
| Nil_construct: List T.

Definition isCons (T: Type) (src: List T) : bool :=
match src with
| Cons_construct _ _ _ => true
| _ => false
end.

Fail Next Obligation.

Hint Unfold  isCons: recognizers. 

Definition isNil (T: Type) (src: List T) : bool :=
match src with
| Nil_construct _ => true
| _ => false
end.

Fail Next Obligation.

Hint Unfold  isNil: recognizers. 

Lemma Cons_exists: (forall T: Type, forall self620: List T, ((true = isCons T self620)) <-> ((exists tmp233: List T, exists tmp232: T, (Cons_construct T tmp232 tmp233 = self620)))). 
Proof.
	repeat t427 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self621: List T, ((true = isNil T self621)) <-> (((Nil_construct T = self621)))). 
Proof.
	repeat t427 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic77 := match goal with 
	| [ H310: (true = isCons ?T ?self622) |- _ ] => 
			poseNew (Mark (T,self622) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H310)
	| [ H310: (isCons ?T ?self622 = true) |- _ ] => 
			poseNew (Mark (T,self622) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H310))
	| [ H311: (true = isNil ?T ?self623) |- _ ] => 
			poseNew (Mark (T,self623) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H311)
	| [ H311: (isNil ?T ?self623 = true) |- _ ] => 
			poseNew (Mark (T,self623) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H311))
	| _ => Option_tactic77
end.

Ltac t428 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac164 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t428.

Definition h (T: Type) (src: Cons_type T) : T :=
match src with
| Cons_construct _ f0 f1 => f0
| _ => let contradiction: False := _ in match contradiction with end
end.

Fail Next Obligation.

Definition t4 (T: Type) (src: Cons_type T) : List T :=
match src with
| Cons_construct _ f0 f1 => f1
| _ => let contradiction: False := _ in match contradiction with end
end.

Fail Next Obligation.


(***********************
  Start of ::
 ***********************)

Definition cons_ (T: Type) (thiss: List T) (t5: T) : List T :=
Cons_construct T t5 thiss.

Fail Next Obligation.

Hint Unfold cons_: definitions.

(***********************
  End of ::
 ***********************)

(***********************
  Start of content
 ***********************)


Definition content_rt39_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt39_type.


Equations content (T: Type) (thiss1: List T) : content_rt39_type T thiss1 := 
	content T thiss1 by rec ignore_termination lt :=
	content T thiss1 := match thiss1 with
	| Nil_construct _ => @set_empty T
	| Cons_construct _ h1 t9 => 
			set_union (set_union (@set_empty T) (set_singleton h1)) (content T t9)
	end.

Hint Unfold content_comp_proj.

Solve Obligations with (repeat t428).
Fail Next Obligation.

Ltac rwrtTac_A165 := match goal with 
	| [ H1477: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B165 := match goal with 
	| [ H1477: context[content ?T ?thiss1], H2477: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			let U165 := (fresh "U") in (poseNew (Mark (T,thiss1) "unfolded content_equation");
			pose proof (content_equation_1 T thiss1) as U165;
			rewrite U165 in *)
	| [ H2477: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			let U165 := (fresh "U") in (poseNew (Mark (T,thiss1) "unfolded content_equation");
			pose proof (content_equation_1 T thiss1) as U165;
			rewrite U165 in *)
end.

Ltac rwrtTac165 := rwrtTac164; repeat rwrtTac_A165; repeat rwrtTac_B165.

Ltac t429 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac165 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t429.

(***********************
  End of content
 ***********************)

(***********************
  Start of contains
 ***********************)


Definition contains_rt6_type (T: Type) (thiss2: List T) (v1: T) : Type :=
{x___2: bool | (Bool.eqb x___2 (set_elem_of v1 (content T thiss2)) = true)}.

Fail Next Obligation.

Hint Unfold contains_rt6_type.


Equations contains (T: Type) (thiss2: List T) (v1: T) : contains_rt6_type T thiss2 v1 := 
	contains T thiss2 v1 by rec ignore_termination lt :=
	contains T thiss2 v1 := match thiss2 with
	| Cons_construct _ h2 t15 => propInBool ((h2 = v1)) || proj1_sig (contains T t15 v1)
	| Nil_construct _ => false
	end.

Hint Unfold contains_comp_proj.

Solve Obligations with (repeat t429).
Fail Next Obligation.

Ltac rwrtTac_A166 := match goal with 
	| [ H1478: context[contains ?T ?thiss2 ?v1] |- _ ] => 
			poseNew (Mark (T,thiss2,v1) "unfolding contains_equation")
	| [  |- context[contains ?T ?thiss2 ?v1] ] => 
			poseNew (Mark (T,thiss2,v1) "unfolding contains_equation")
end.

Ltac rwrtTac_B166 := match goal with 
	| [ H1478: context[contains ?T ?thiss2 ?v1], H2478: Marked (?T,?thiss2,?v1) "unfolding contains_equation" |- _ ] => 
			let U166 := (fresh "U") in (poseNew (Mark (T,thiss2,v1) "unfolded contains_equation");
			pose proof (contains_equation_1 T thiss2 v1) as U166;
			rewrite U166 in *)
	| [ H2478: Marked (?T,?thiss2,?v1) "unfolding contains_equation" |- context[contains ?T ?thiss2 ?v1] ] => 
			let U166 := (fresh "U") in (poseNew (Mark (T,thiss2,v1) "unfolded contains_equation");
			pose proof (contains_equation_1 T thiss2 v1) as U166;
			rewrite U166 in *)
end.

Ltac rwrtTac166 := rwrtTac165; repeat rwrtTac_A166; repeat rwrtTac_B166.

Ltac t430 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac166 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t430.

(***********************
  End of contains
 ***********************)

(***********************
  Start of empty
 ***********************)

Definition empty (A: Type) (B: Type) : map_type A (Option B) :=
magic (map_type A (Option B)).

Fail Next Obligation.

Hint Unfold empty: definitions.

(***********************
  End of empty
 ***********************)

(***********************
  Start of filter
 ***********************)

Definition filter (T: Type) (thiss3: Option T) (p: T -> bool) : Option T :=
ifthenelse
	(ifthenelse (isSome _ thiss3) bool
		(fun _ => p (v T thiss3) )
		(fun _ => false ))
	(Option T)
	(fun _ => Some_construct T (v T thiss3) )
	(fun _ => None_construct T ).

Fail Next Obligation.

Hint Unfold filter: definitions.

(***********************
  End of filter
 ***********************)

(***********************
  Start of find
 ***********************)


Definition find_rt1_type (T: Type) (thiss4: List T) (p1: T -> bool) : Type :=
{res: Option T | (match res with
| Some_construct _ r => 
		ifthenelse (set_elem_of r (content T thiss4)) bool
			(fun _ => p1 r )
			(fun _ => false )
| None_construct _ => true
end = true)}.

Fail Next Obligation.

Hint Unfold find_rt1_type.


Equations find (T: Type) (thiss4: List T) (p1: T -> bool) : find_rt1_type T thiss4 p1 := 
	find T thiss4 p1 by rec ignore_termination lt :=
	find T thiss4 p1 := match thiss4 with
	| Nil_construct _ => None_construct T
	| Cons_construct _ h3 t27 => 
			ifthenelse (p1 h3) (Option T)
				(fun _ => Some_construct T h3 )
				(fun _ => proj1_sig (find T t27 p1) )
	end.

Hint Unfold find_comp_proj.

Solve Obligations with (repeat t430).
Fail Next Obligation.

Ltac rwrtTac_A167 := match goal with 
	| [ H1479: context[find ?T ?thiss4 ?p1] |- _ ] => 
			poseNew (Mark (T,thiss4,p1) "unfolding find_equation")
	| [  |- context[find ?T ?thiss4 ?p1] ] => 
			poseNew (Mark (T,thiss4,p1) "unfolding find_equation")
end.

Ltac rwrtTac_B167 := match goal with 
	| [ H1479: context[find ?T ?thiss4 ?p1], H2479: Marked (?T,?thiss4,?p1) "unfolding find_equation" |- _ ] => 
			let U167 := (fresh "U") in (poseNew (Mark (T,thiss4,p1) "unfolded find_equation");
			pose proof (find_equation_1 T thiss4 p1) as U167;
			rewrite U167 in *)
	| [ H2479: Marked (?T,?thiss4,?p1) "unfolding find_equation" |- context[find ?T ?thiss4 ?p1] ] => 
			let U167 := (fresh "U") in (poseNew (Mark (T,thiss4,p1) "unfolded find_equation");
			pose proof (find_equation_1 T thiss4 p1) as U167;
			rewrite U167 in *)
end.

Ltac rwrtTac167 := rwrtTac166; repeat rwrtTac_A167; repeat rwrtTac_B167.

Ltac t431 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac167 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t431.

(***********************
  End of find
 ***********************)

(***********************
  Start of flatMap
 ***********************)

Definition flatMap (T: Type) (R: Type) (thiss5: Option T) (f: T -> (Option R)) : Option R :=
match thiss5 with
| None_construct _ => None_construct R
| Some_construct _ x => f x
end.

Fail Next Obligation.

Hint Unfold flatMap: definitions.

(***********************
  End of flatMap
 ***********************)

(***********************
  Start of foldLeft
 ***********************)


Definition foldLeft_rt2_type (T: Type) (R: Type) (thiss6: List T) (z: R) (f1: R -> (T -> R)) : Type :=
R.

Fail Next Obligation.

Hint Unfold foldLeft_rt2_type.


Equations foldLeft (T: Type) (R: Type) (thiss6: List T) (z: R) (f1: R -> (T -> R)) : foldLeft_rt2_type T R thiss6 z f1 := 
	foldLeft T R thiss6 z f1 by rec ignore_termination lt :=
	foldLeft T R thiss6 z f1 := match thiss6 with
	| Nil_construct _ => z
	| Cons_construct _ h4 t35 => foldLeft T R t35 (f1 z h4) f1
	end.

Hint Unfold foldLeft_comp_proj.

Solve Obligations with (repeat t431).
Fail Next Obligation.

Ltac rwrtTac_A168 := match goal with 
	| [ H1480: context[foldLeft ?T ?R ?thiss6 ?z ?f1] |- _ ] => 
			poseNew (Mark (T,R,thiss6,z,f1) "unfolding foldLeft_equation")
	| [  |- context[foldLeft ?T ?R ?thiss6 ?z ?f1] ] => 
			poseNew (Mark (T,R,thiss6,z,f1) "unfolding foldLeft_equation")
end.

Ltac rwrtTac_B168 := match goal with 
	| [ H1480: context[foldLeft ?T ?R ?thiss6 ?z ?f1], H2480: Marked (?T,?R,?thiss6,?z,?f1) "unfolding foldLeft_equation" |- _ ] => 
			let U168 := (fresh "U") in (poseNew (Mark (T,R,thiss6,z,f1) "unfolded foldLeft_equation");
			pose proof (foldLeft_equation_1 T R thiss6 z f1) as U168;
			rewrite U168 in *)
	| [ H2480: Marked (?T,?R,?thiss6,?z,?f1) "unfolding foldLeft_equation" |- context[foldLeft ?T ?R ?thiss6 ?z ?f1] ] => 
			let U168 := (fresh "U") in (poseNew (Mark (T,R,thiss6,z,f1) "unfolded foldLeft_equation");
			pose proof (foldLeft_equation_1 T R thiss6 z f1) as U168;
			rewrite U168 in *)
end.

Ltac rwrtTac168 := rwrtTac167; repeat rwrtTac_A168; repeat rwrtTac_B168.

Ltac t432 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac168 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t432.

(***********************
  End of foldLeft
 ***********************)

(***********************
  Start of foldRight
 ***********************)


Definition foldRight_rt1_type (T: Type) (R: Type) (thiss7: List T) (z1: R) (f2: T -> (R -> R)) : Type :=
R.

Fail Next Obligation.

Hint Unfold foldRight_rt1_type.


Equations foldRight (T: Type) (R: Type) (thiss7: List T) (z1: R) (f2: T -> (R -> R)) : foldRight_rt1_type T R thiss7 z1 f2 := 
	foldRight T R thiss7 z1 f2 by rec ignore_termination lt :=
	foldRight T R thiss7 z1 f2 := match thiss7 with
	| Nil_construct _ => z1
	| Cons_construct _ h5 t40 => f2 h5 (foldRight T R t40 z1 f2)
	end.

Hint Unfold foldRight_comp_proj.

Solve Obligations with (repeat t432).
Fail Next Obligation.

Ltac rwrtTac_A169 := match goal with 
	| [ H1481: context[foldRight ?T ?R ?thiss7 ?z1 ?f2] |- _ ] => 
			poseNew (Mark (T,R,thiss7,z1,f2) "unfolding foldRight_equation")
	| [  |- context[foldRight ?T ?R ?thiss7 ?z1 ?f2] ] => 
			poseNew (Mark (T,R,thiss7,z1,f2) "unfolding foldRight_equation")
end.

Ltac rwrtTac_B169 := match goal with 
	| [ H1481: context[foldRight ?T ?R ?thiss7 ?z1 ?f2], H2481: Marked (?T,?R,?thiss7,?z1,?f2) "unfolding foldRight_equation" |- _ ] => 
			let U169 := (fresh "U") in (poseNew (Mark (T,R,thiss7,z1,f2) "unfolded foldRight_equation");
			pose proof (foldRight_equation_1 T R thiss7 z1 f2) as U169;
			rewrite U169 in *)
	| [ H2481: Marked (?T,?R,?thiss7,?z1,?f2) "unfolding foldRight_equation" |- context[foldRight ?T ?R ?thiss7 ?z1 ?f2] ] => 
			let U169 := (fresh "U") in (poseNew (Mark (T,R,thiss7,z1,f2) "unfolded foldRight_equation");
			pose proof (foldRight_equation_1 T R thiss7 z1 f2) as U169;
			rewrite U169 in *)
end.

Ltac rwrtTac169 := rwrtTac168; repeat rwrtTac_A169; repeat rwrtTac_B169.

Ltac t433 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac169 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t433.

(***********************
  End of foldRight
 ***********************)

(***********************
  Start of forall
 ***********************)

Definition _forall (T: Type) (thiss8: Option T) (p2: T -> bool) : bool :=
ifthenelse
	(ifthenelse (isSome _ thiss8) bool
		(fun _ => negb (p2 (v T thiss8)) )
		(fun _ => false ))
	bool
	(fun _ => false )
	(fun _ => true ).

Fail Next Obligation.

Hint Unfold _forall: definitions.

(***********************
  End of forall
 ***********************)

(***********************
  Start of exists
 ***********************)

Definition _exists (T: Type) (thiss9: Option T) (p3: T -> bool) : bool :=
negb (_forall T thiss9 (fun x___3 => negb (p3 x___3) )).

Fail Next Obligation.

Hint Unfold _exists: definitions.

(***********************
  End of exists
 ***********************)

(***********************
  Start of forall
 ***********************)


Definition forall1_rt9_type (T: Type) (thiss10: List T) (p4: T -> bool) : Type :=
bool.

Fail Next Obligation.

Hint Unfold forall1_rt9_type.


Equations forall1 (T: Type) (thiss10: List T) (p4: T -> bool) : forall1_rt9_type T thiss10 p4 := 
	forall1 T thiss10 p4 by rec ignore_termination lt :=
	forall1 T thiss10 p4 := match thiss10 with
	| Nil_construct _ => true
	| Cons_construct _ h6 t51 => 
			ifthenelse (p4 h6) bool
				(fun _ => forall1 T t51 p4 )
				(fun _ => false )
	end.

Hint Unfold forall1_comp_proj.

Solve Obligations with (repeat t433).
Fail Next Obligation.

Ltac rwrtTac_A170 := match goal with 
	| [ H1482: context[forall1 ?T ?thiss10 ?p4] |- _ ] => 
			poseNew (Mark (T,thiss10,p4) "unfolding forall1_equation")
	| [  |- context[forall1 ?T ?thiss10 ?p4] ] => 
			poseNew (Mark (T,thiss10,p4) "unfolding forall1_equation")
end.

Ltac rwrtTac_B170 := match goal with 
	| [ H1482: context[forall1 ?T ?thiss10 ?p4], H2482: Marked (?T,?thiss10,?p4) "unfolding forall1_equation" |- _ ] => 
			let U170 := (fresh "U") in (poseNew (Mark (T,thiss10,p4) "unfolded forall1_equation");
			pose proof (forall1_equation_1 T thiss10 p4) as U170;
			rewrite U170 in *)
	| [ H2482: Marked (?T,?thiss10,?p4) "unfolding forall1_equation" |- context[forall1 ?T ?thiss10 ?p4] ] => 
			let U170 := (fresh "U") in (poseNew (Mark (T,thiss10,p4) "unfolded forall1_equation");
			pose proof (forall1_equation_1 T thiss10 p4) as U170;
			rewrite U170 in *)
end.

Ltac rwrtTac170 := rwrtTac169; repeat rwrtTac_A170; repeat rwrtTac_B170.

Ltac t434 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac170 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t434.

(***********************
  End of forall
 ***********************)

(***********************
  Start of exists
 ***********************)

Definition exists1 (T: Type) (thiss11: List T) (p5: T -> bool) : bool :=
negb (forall1 T thiss11 (fun x___22 => negb (p5 x___22) )).

Fail Next Obligation.

Hint Unfold exists1: definitions.

(***********************
  End of exists
 ***********************)

(***********************
  Start of getOrElse
 ***********************)

Definition getOrElse (T: Type) (thiss12: Option T) (default: T) : T :=
match thiss12 with
| Some_construct _ v2 => v2
| None_construct _ => default
end.

Fail Next Obligation.

Hint Unfold getOrElse: definitions.

(***********************
  End of getOrElse
 ***********************)

(***********************
  Start of groupBy
 ***********************)


Definition groupBy_rt1_type (T: Type) (R: Type) (thiss13: List T) (f3: T -> R) : Type :=
map_type R (Option (List T)).

Fail Next Obligation.

Hint Unfold groupBy_rt1_type.


Equations groupBy (T: Type) (R: Type) (thiss13: List T) (f3: T -> R) : groupBy_rt1_type T R thiss13 f3 := 
	groupBy T R thiss13 f3 by rec ignore_termination lt :=
	groupBy T R thiss13 f3 := match thiss13 with
	| Nil_construct _ => magic (map_type R (Option (List T)))
	| Cons_construct _ h7 t63 => 
			let key := (f3 h7) in (let rest := (groupBy T R t63 f3) in (let prev := (ifthenelse (negb (propInBool ((magic (Option (List T)) = None_construct (List T))))) (List T)
				(fun _ => magic (List T) )
				(fun _ => Nil_construct T )) in (magic (map_type R (Option (List T))))))
	end.

Hint Unfold groupBy_comp_proj.

Solve Obligations with (repeat t434).
Fail Next Obligation.

Ltac rwrtTac_A171 := match goal with 
	| [ H1483: context[groupBy ?T ?R ?thiss13 ?f3] |- _ ] => 
			poseNew (Mark (T,R,thiss13,f3) "unfolding groupBy_equation")
	| [  |- context[groupBy ?T ?R ?thiss13 ?f3] ] => 
			poseNew (Mark (T,R,thiss13,f3) "unfolding groupBy_equation")
end.

Ltac rwrtTac_B171 := match goal with 
	| [ H1483: context[groupBy ?T ?R ?thiss13 ?f3], H2483: Marked (?T,?R,?thiss13,?f3) "unfolding groupBy_equation" |- _ ] => 
			let U171 := (fresh "U") in (poseNew (Mark (T,R,thiss13,f3) "unfolded groupBy_equation");
			pose proof (groupBy_equation_1 T R thiss13 f3) as U171;
			rewrite U171 in *)
	| [ H2483: Marked (?T,?R,?thiss13,?f3) "unfolding groupBy_equation" |- context[groupBy ?T ?R ?thiss13 ?f3] ] => 
			let U171 := (fresh "U") in (poseNew (Mark (T,R,thiss13,f3) "unfolded groupBy_equation");
			pose proof (groupBy_equation_1 T R thiss13 f3) as U171;
			rewrite U171 in *)
end.

Ltac rwrtTac171 := rwrtTac170; repeat rwrtTac_A171; repeat rwrtTac_B171.

Ltac t435 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac171 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t435.

(***********************
  End of groupBy
 ***********************)

(***********************
  Start of head
 ***********************)

Definition head (T: Type) (thiss14: List T) (contractHyp259: (negb (propInBool ((thiss14 = Nil_construct T))) = true)) : T :=
ifthenelse (isCons _ thiss14) T
	(fun _ => h T thiss14 )
	(fun _ => let contradiction: False := _ in match contradiction with end ).

Fail Next Obligation.

Hint Unfold head: definitions.

(***********************
  End of head
 ***********************)

(***********************
  Start of indexOf
 ***********************)


Definition indexOf_rt1_type (T: Type) (thiss15: List T) (elem: T) : Type :=
{res1: Z | (Bool.eqb (Z.geb res1 (0)%Z) (set_elem_of elem (content T thiss15)) = true)}.

Fail Next Obligation.

Hint Unfold indexOf_rt1_type.


Equations indexOf (T: Type) (thiss15: List T) (elem: T) : indexOf_rt1_type T thiss15 elem := 
	indexOf T thiss15 elem by rec ignore_termination lt :=
	indexOf T thiss15 elem := ifthenelse (isNil _ thiss15) Z
		(fun _ => (-1)%Z )
		(fun _ => ifthenelse
			(ifthenelse (isCons _ thiss15) bool
				(fun _ => propInBool ((h T thiss15 = elem)) )
				(fun _ => false ))
			Z
			(fun _ => (0)%Z )
			(fun _ => ifthenelse (isCons _ thiss15) Z
				(fun _ => let rec := (proj1_sig (indexOf T (t4 T thiss15) elem)) in (ifthenelse (Zeq_bool rec (-1)%Z) Z
					(fun _ => (-1)%Z )
					(fun _ => Z.add rec (1)%Z )) )
				(fun _ => let contradiction: False := _ in match contradiction with end ) ) ).

Hint Unfold indexOf_comp_proj.

Solve Obligations with (repeat t435).
Fail Next Obligation.

Ltac rwrtTac_A172 := match goal with 
	| [ H1484: context[indexOf ?T ?thiss15 ?elem] |- _ ] => 
			poseNew (Mark (T,thiss15,elem) "unfolding indexOf_equation")
	| [  |- context[indexOf ?T ?thiss15 ?elem] ] => 
			poseNew (Mark (T,thiss15,elem) "unfolding indexOf_equation")
end.

Ltac rwrtTac_B172 := match goal with 
	| [ H1484: context[indexOf ?T ?thiss15 ?elem], H2484: Marked (?T,?thiss15,?elem) "unfolding indexOf_equation" |- _ ] => 
			let U172 := (fresh "U") in (poseNew (Mark (T,thiss15,elem) "unfolded indexOf_equation");
			pose proof (indexOf_equation_1 T thiss15 elem) as U172;
			rewrite U172 in *)
	| [ H2484: Marked (?T,?thiss15,?elem) "unfolding indexOf_equation" |- context[indexOf ?T ?thiss15 ?elem] ] => 
			let U172 := (fresh "U") in (poseNew (Mark (T,thiss15,elem) "unfolded indexOf_equation");
			pose proof (indexOf_equation_1 T thiss15 elem) as U172;
			rewrite U172 in *)
end.

Ltac rwrtTac172 := rwrtTac171; repeat rwrtTac_A172; repeat rwrtTac_B172.

Ltac t436 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac172 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t436.

(***********************
  End of indexOf
 ***********************)

(***********************
  Start of indexWhere
 ***********************)


Definition indexWhere_rt1_type (T: Type) (thiss16: List T) (p6: T -> bool) : Type :=
{x___25: Z | (Bool.eqb (Z.geb x___25 (0)%Z) (exists1 T thiss16 p6) = true)}.

Fail Next Obligation.

Hint Unfold indexWhere_rt1_type.


Equations indexWhere (T: Type) (thiss16: List T) (p6: T -> bool) : indexWhere_rt1_type T thiss16 p6 := 
	indexWhere T thiss16 p6 by rec ignore_termination lt :=
	indexWhere T thiss16 p6 := ifthenelse (isNil _ thiss16) Z
		(fun _ => (-1)%Z )
		(fun _ => ifthenelse
			(ifthenelse (isCons _ thiss16) bool
				(fun _ => p6 (h T thiss16) )
				(fun _ => false ))
			Z
			(fun _ => (0)%Z )
			(fun _ => ifthenelse (isCons _ thiss16) Z
				(fun _ => let rec1 := (proj1_sig (indexWhere T (t4 T thiss16) p6)) in (ifthenelse (Z.geb rec1 (0)%Z) Z
					(fun _ => Z.add rec1 (1)%Z )
					(fun _ => (-1)%Z )) )
				(fun _ => let contradiction: False := _ in match contradiction with end ) ) ).

Hint Unfold indexWhere_comp_proj.

Solve Obligations with (repeat t436).
Fail Next Obligation.

Ltac rwrtTac_A173 := match goal with 
	| [ H1485: context[indexWhere ?T ?thiss16 ?p6] |- _ ] => 
			poseNew (Mark (T,thiss16,p6) "unfolding indexWhere_equation")
	| [  |- context[indexWhere ?T ?thiss16 ?p6] ] => 
			poseNew (Mark (T,thiss16,p6) "unfolding indexWhere_equation")
end.

Ltac rwrtTac_B173 := match goal with 
	| [ H1485: context[indexWhere ?T ?thiss16 ?p6], H2485: Marked (?T,?thiss16,?p6) "unfolding indexWhere_equation" |- _ ] => 
			let U173 := (fresh "U") in (poseNew (Mark (T,thiss16,p6) "unfolded indexWhere_equation");
			pose proof (indexWhere_equation_1 T thiss16 p6) as U173;
			rewrite U173 in *)
	| [ H2485: Marked (?T,?thiss16,?p6) "unfolding indexWhere_equation" |- context[indexWhere ?T ?thiss16 ?p6] ] => 
			let U173 := (fresh "U") in (poseNew (Mark (T,thiss16,p6) "unfolded indexWhere_equation");
			pose proof (indexWhere_equation_1 T thiss16 p6) as U173;
			rewrite U173 in *)
end.

Ltac rwrtTac173 := rwrtTac172; repeat rwrtTac_A173; repeat rwrtTac_B173.

Ltac t437 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac173 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t437.

(***********************
  End of indexWhere
 ***********************)

(***********************
  Start of isEmpty
 ***********************)

Definition isEmpty (T: Type) (thiss17: List T) : bool :=
ifthenelse (isNil _ thiss17) bool
	(fun _ => true )
	(fun _ => false ).

Fail Next Obligation.

Hint Unfold isEmpty: definitions.

(***********************
  End of isEmpty
 ***********************)

(***********************
  Start of isEmpty
 ***********************)

Definition isEmpty1 (T: Type) (thiss18: Option T) : bool :=
propInBool ((thiss18 = None_construct T)).

Fail Next Obligation.

Hint Unfold isEmpty1: definitions.

(***********************
  End of isEmpty
 ***********************)

(***********************
  Start of isDefined
 ***********************)

Definition isDefined (T: Type) (thiss19: Option T) : bool :=
negb (isEmpty1 T thiss19).

Fail Next Obligation.

Hint Unfold isDefined: definitions.

(***********************
  End of isDefined
 ***********************)

(***********************
  Start of get
 ***********************)

Definition get (T: Type) (thiss20: Option T) (contractHyp265: (isDefined T thiss20 = true)) : T :=
ifthenelse (isSome _ thiss20) T
	(fun _ => v T thiss20 )
	(fun _ => let contradiction: False := _ in match contradiction with end ).

Fail Next Obligation.

Hint Unfold get: definitions.

(***********************
  End of get
 ***********************)

(***********************
  Start of headOption
 ***********************)

Definition headOption (T: Type) (thiss21: List T) : {x___5: Option T | (negb (Bool.eqb (isDefined T x___5) (isEmpty T thiss21)) = true)} :=
match thiss21 with
| Cons_construct _ h8 t93 => Some_construct T h8
| Nil_construct _ => None_construct T
end.

Fail Next Obligation.

Hint Unfold headOption: definitions.

(***********************
  End of headOption
 ***********************)

(***********************
  Start of last
 ***********************)


Definition contractHyp267_type (T: Type) (thiss22: List T) : Type :=
(negb (isEmpty T thiss22) = true).

Fail Next Obligation.

Hint Unfold contractHyp267_type.


Definition last_rt1_type (T: Type) (thiss22: List T) (contractHyp267: contractHyp267_type T thiss22) : Type :=
{v3: T | (proj1_sig (contains T thiss22 v3) = true)}.

Fail Next Obligation.

Hint Unfold last_rt1_type.


Equations last (T: Type) (thiss22: List T) (contractHyp267: contractHyp267_type T thiss22) : last_rt1_type T thiss22 contractHyp267 := 
	last T thiss22 contractHyp267 by rec ignore_termination lt :=
	last T thiss22 contractHyp267 := ifthenelse
		(ifthenelse (isCons _ thiss22) bool
			(fun _ => isNil _ (t4 T thiss22) )
			(fun _ => false ))
		T
		(fun _ => h T thiss22 )
		(fun _ => ifthenelse (isCons _ thiss22) T
			(fun _ => proj1_sig (last T (t4 T thiss22) _) )
			(fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold last_comp_proj.

Solve Obligations with (repeat t437).
Fail Next Obligation.

Ltac rwrtTac_A174 := match goal with 
	| [ H1486: context[last ?T ?thiss22] |- _ ] => 
			poseNew (Mark (T,thiss22) "unfolding last_equation")
	| [  |- context[last ?T ?thiss22] ] => 
			poseNew (Mark (T,thiss22) "unfolding last_equation")
end.

Ltac rwrtTac_B174 := match goal with 
	| [ H1486: context[last ?T ?thiss22], H2486: Marked (?T,?thiss22) "unfolding last_equation" |- _ ] => 
			let U174 := (fresh "U") in (poseNew (Mark (T,thiss22) "unfolded last_equation");
			pose proof (last_equation_1 T thiss22) as U174;
			rewrite U174 in *)
	| [ H2486: Marked (?T,?thiss22) "unfolding last_equation" |- context[last ?T ?thiss22] ] => 
			let U174 := (fresh "U") in (poseNew (Mark (T,thiss22) "unfolded last_equation");
			pose proof (last_equation_1 T thiss22) as U174;
			rewrite U174 in *)
end.

Ltac rwrtTac174 := rwrtTac173; repeat rwrtTac_A174; repeat rwrtTac_B174.

Ltac t438 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac174 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t438.

(***********************
  End of last
 ***********************)

(***********************
  Start of map
 ***********************)

Definition map (T: Type) (R: Type) (thiss23: Option T) (f4: T -> R) : {x___21: Option R | (Bool.eqb (isDefined R x___21) (isDefined T thiss23) = true)} :=
match thiss23 with
| None_construct _ => None_construct R
| Some_construct _ x1 => Some_construct R (f4 x1)
end.

Fail Next Obligation.

Hint Unfold map: definitions.

(***********************
  End of map
 ***********************)

(***********************
  Start of nonEmpty
 ***********************)

Definition nonEmpty (T: Type) (thiss24: Option T) : bool :=
negb (isEmpty1 T thiss24).

Fail Next Obligation.

Hint Unfold nonEmpty: definitions.

(***********************
  End of nonEmpty
 ***********************)

(***********************
  Start of nonEmpty
 ***********************)

Definition nonEmpty1 (T: Type) (thiss25: List T) : bool :=
negb (isEmpty T thiss25).

Fail Next Obligation.

Hint Unfold nonEmpty1: definitions.

(***********************
  End of nonEmpty
 ***********************)

(***********************
  Start of orElse
 ***********************)

Definition orElse (T: Type) (thiss26: Option T) (or: Option T) : {x___1: Option T | (Bool.eqb (isDefined T x___1) (isDefined T thiss26) || isDefined T or = true)} :=
match thiss26 with
| Some_construct _ v4 => thiss26
| None_construct _ => or
end.

Fail Next Obligation.

Hint Unfold orElse: definitions.

(***********************
  End of orElse
 ***********************)

(***********************
  Start of lastOption
 ***********************)


Definition lastOption_rt1_type (T: Type) (thiss27: List T) : Type :=
{x___4: Option T | (negb (Bool.eqb (isDefined T x___4) (isEmpty T thiss27)) = true)}.

Fail Next Obligation.

Hint Unfold lastOption_rt1_type.


Equations lastOption (T: Type) (thiss27: List T) : lastOption_rt1_type T thiss27 := 
	lastOption T thiss27 by rec ignore_termination lt :=
	lastOption T thiss27 := match thiss27 with
	| Cons_construct _ h9 t115 => 
			proj1_sig (orElse T (proj1_sig (lastOption T t115)) (Some_construct T h9))
	| Nil_construct _ => None_construct T
	end.

Hint Unfold lastOption_comp_proj.

Solve Obligations with (repeat t438).
Fail Next Obligation.

Ltac rwrtTac_A175 := match goal with 
	| [ H1487: context[lastOption ?T ?thiss27] |- _ ] => 
			poseNew (Mark (T,thiss27) "unfolding lastOption_equation")
	| [  |- context[lastOption ?T ?thiss27] ] => 
			poseNew (Mark (T,thiss27) "unfolding lastOption_equation")
end.

Ltac rwrtTac_B175 := match goal with 
	| [ H1487: context[lastOption ?T ?thiss27], H2487: Marked (?T,?thiss27) "unfolding lastOption_equation" |- _ ] => 
			let U175 := (fresh "U") in (poseNew (Mark (T,thiss27) "unfolded lastOption_equation");
			pose proof (lastOption_equation_1 T thiss27) as U175;
			rewrite U175 in *)
	| [ H2487: Marked (?T,?thiss27) "unfolding lastOption_equation" |- context[lastOption ?T ?thiss27] ] => 
			let U175 := (fresh "U") in (poseNew (Mark (T,thiss27) "unfolded lastOption_equation");
			pose proof (lastOption_equation_1 T thiss27) as U175;
			rewrite U175 in *)
end.

Ltac rwrtTac175 := rwrtTac174; repeat rwrtTac_A175; repeat rwrtTac_B175.

Ltac t439 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac175 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t439.

(***********************
  End of lastOption
 ***********************)

(***********************
  Start of scanLeft
 ***********************)


Definition scanLeft_rt1_type (T: Type) (R: Type) (thiss28: List T) (z2: R) (f5: R -> (T -> R)) : Type :=
{x___12: List R | (negb (isEmpty R x___12) = true)}.

Fail Next Obligation.

Hint Unfold scanLeft_rt1_type.


Equations scanLeft (T: Type) (R: Type) (thiss28: List T) (z2: R) (f5: R -> (T -> R)) : scanLeft_rt1_type T R thiss28 z2 f5 := 
	scanLeft T R thiss28 z2 f5 by rec ignore_termination lt :=
	scanLeft T R thiss28 z2 f5 := match thiss28 with
	| Nil_construct _ => cons_ R (Nil_construct R) z2
	| Cons_construct _ h10 t120 => 
			cons_ R (proj1_sig (scanLeft T R t120 (f5 z2 h10) f5)) z2
	end.

Hint Unfold scanLeft_comp_proj.

Solve Obligations with (repeat t439).
Fail Next Obligation.

Ltac rwrtTac_A176 := match goal with 
	| [ H1488: context[scanLeft ?T ?R ?thiss28 ?z2 ?f5] |- _ ] => 
			poseNew (Mark (T,R,thiss28,z2,f5) "unfolding scanLeft_equation")
	| [  |- context[scanLeft ?T ?R ?thiss28 ?z2 ?f5] ] => 
			poseNew (Mark (T,R,thiss28,z2,f5) "unfolding scanLeft_equation")
end.

Ltac rwrtTac_B176 := match goal with 
	| [ H1488: context[scanLeft ?T ?R ?thiss28 ?z2 ?f5], H2488: Marked (?T,?R,?thiss28,?z2,?f5) "unfolding scanLeft_equation" |- _ ] => 
			let U176 := (fresh "U") in (poseNew (Mark (T,R,thiss28,z2,f5) "unfolded scanLeft_equation");
			pose proof (scanLeft_equation_1 T R thiss28 z2 f5) as U176;
			rewrite U176 in *)
	| [ H2488: Marked (?T,?R,?thiss28,?z2,?f5) "unfolding scanLeft_equation" |- context[scanLeft ?T ?R ?thiss28 ?z2 ?f5] ] => 
			let U176 := (fresh "U") in (poseNew (Mark (T,R,thiss28,z2,f5) "unfolded scanLeft_equation");
			pose proof (scanLeft_equation_1 T R thiss28 z2 f5) as U176;
			rewrite U176 in *)
end.

Ltac rwrtTac176 := rwrtTac175; repeat rwrtTac_A176; repeat rwrtTac_B176.

Ltac t440 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac176 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t440.

(***********************
  End of scanLeft
 ***********************)

(***********************
  Start of scanRight
 ***********************)


Definition scanRight_rt1_type (T: Type) (R: Type) (thiss29: List T) (z3: R) (f6: T -> (R -> R)) : Type :=
{x___16: List R | (negb (isEmpty R x___16) = true)}.

Fail Next Obligation.

Hint Unfold scanRight_rt1_type.


Equations scanRight (T: Type) (R: Type) (thiss29: List T) (z3: R) (f6: T -> (R -> R)) : scanRight_rt1_type T R thiss29 z3 f6 := 
	scanRight T R thiss29 z3 f6 by rec ignore_termination lt :=
	scanRight T R thiss29 z3 f6 := match thiss29 with
	| Nil_construct _ => cons_ R (Nil_construct R) z3
	| Cons_construct _ h11 t125 => 
			let x___14 := (ifthenelse (isCons _ (proj1_sig (scanRight T R t125 z3 f6))) (((List R) * R)%type)
				(fun _ => (proj1_sig (scanRight T R t125 z3 f6),h R (proj1_sig (scanRight T R t125 z3 f6))) )
				(fun _ => let contradiction: False := _ in match contradiction with end )) in (let h1 := (snd x___14) in (let x___15 := (f6 h11 h1) in (cons_ R (fst x___14) x___15)))
	end.

Hint Unfold scanRight_comp_proj.

Solve Obligations with (repeat t440).
Fail Next Obligation.

Ltac rwrtTac_A177 := match goal with 
	| [ H1489: context[scanRight ?T ?R ?thiss29 ?z3 ?f6] |- _ ] => 
			poseNew (Mark (T,R,thiss29,z3,f6) "unfolding scanRight_equation")
	| [  |- context[scanRight ?T ?R ?thiss29 ?z3 ?f6] ] => 
			poseNew (Mark (T,R,thiss29,z3,f6) "unfolding scanRight_equation")
end.

Ltac rwrtTac_B177 := match goal with 
	| [ H1489: context[scanRight ?T ?R ?thiss29 ?z3 ?f6], H2489: Marked (?T,?R,?thiss29,?z3,?f6) "unfolding scanRight_equation" |- _ ] => 
			let U177 := (fresh "U") in (poseNew (Mark (T,R,thiss29,z3,f6) "unfolded scanRight_equation");
			pose proof (scanRight_equation_1 T R thiss29 z3 f6) as U177;
			rewrite U177 in *)
	| [ H2489: Marked (?T,?R,?thiss29,?z3,?f6) "unfolding scanRight_equation" |- context[scanRight ?T ?R ?thiss29 ?z3 ?f6] ] => 
			let U177 := (fresh "U") in (poseNew (Mark (T,R,thiss29,z3,f6) "unfolded scanRight_equation");
			pose proof (scanRight_equation_1 T R thiss29 z3 f6) as U177;
			rewrite U177 in *)
end.

Ltac rwrtTac177 := rwrtTac176; repeat rwrtTac_A177; repeat rwrtTac_B177.

Ltac t441 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac177 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t441.

(***********************
  End of scanRight
 ***********************)

(***********************
  Start of size
 ***********************)


Definition size_rt38_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt38_type.


Equations size (T: Type) (thiss30: List T) : size_rt38_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t130 => Z.add (1)%Z (proj1_sig (size T t130))
	end.

Hint Unfold size_comp_proj.

Solve Obligations with (repeat t441).
Fail Next Obligation.

Ltac rwrtTac_A178 := match goal with 
	| [ H1490: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B178 := match goal with 
	| [ H1490: context[size ?T ?thiss30], H2490: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			let U178 := (fresh "U") in (poseNew (Mark (T,thiss30) "unfolded size_equation");
			pose proof (size_equation_1 T thiss30) as U178;
			rewrite U178 in *)
	| [ H2490: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			let U178 := (fresh "U") in (poseNew (Mark (T,thiss30) "unfolded size_equation");
			pose proof (size_equation_1 T thiss30) as U178;
			rewrite U178 in *)
end.

Ltac rwrtTac178 := rwrtTac177; repeat rwrtTac_A178; repeat rwrtTac_B178.

Ltac t442 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac178 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t442.

(***********************
  End of size
 ***********************)

(***********************
  Start of &
 ***********************)


Definition c__rt1_type (T: Type) (thiss31: List T) (that: List T) : Type :=
{res2: List T | (ifthenelse (Z.leb (proj1_sig (size T res2)) (proj1_sig (size T thiss31))) bool
	(fun _ => set_equality (content T res2) (set_intersection (content T thiss31) (content T that)) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold c__rt1_type.


Equations c_ (T: Type) (thiss31: List T) (that: List T) : c__rt1_type T thiss31 that := 
	c_ T thiss31 that by rec ignore_termination lt :=
	c_ T thiss31 that := match thiss31 with
	| Cons_construct _ h13 t138 => 
			ifthenelse (proj1_sig (contains T that h13)) (List T)
				(fun _ => Cons_construct T h13 (proj1_sig (c_ T t138 that)) )
				(fun _ => proj1_sig (c_ T t138 that) )
	| Nil_construct _ => Nil_construct T
	end.

Hint Unfold c__comp_proj.

Solve Obligations with (repeat t442).
Fail Next Obligation.

Ltac rwrtTac_A179 := match goal with 
	| [ H1491: context[c_ ?T ?thiss31 ?that] |- _ ] => 
			poseNew (Mark (T,thiss31,that) "unfolding c__equation")
	| [  |- context[c_ ?T ?thiss31 ?that] ] => 
			poseNew (Mark (T,thiss31,that) "unfolding c__equation")
end.

Ltac rwrtTac_B179 := match goal with 
	| [ H1491: context[c_ ?T ?thiss31 ?that], H2491: Marked (?T,?thiss31,?that) "unfolding c__equation" |- _ ] => 
			let U179 := (fresh "U") in (poseNew (Mark (T,thiss31,that) "unfolded c__equation");
			pose proof (c__equation_1 T thiss31 that) as U179;
			rewrite U179 in *)
	| [ H2491: Marked (?T,?thiss31,?that) "unfolding c__equation" |- context[c_ ?T ?thiss31 ?that] ] => 
			let U179 := (fresh "U") in (poseNew (Mark (T,thiss31,that) "unfolded c__equation");
			pose proof (c__equation_1 T thiss31 that) as U179;
			rewrite U179 in *)
end.

Ltac rwrtTac179 := rwrtTac178; repeat rwrtTac_A179; repeat rwrtTac_B179.

Ltac t443 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac179 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t443.

(***********************
  End of &
 ***********************)

(***********************
  Start of ++
 ***********************)


Definition plus_plus__rt10_type (T: Type) (thiss32: List T) (that1: List T) : Type :=
{res3: List T | (ifthenelse
	(ifthenelse (set_equality (content T res3) (set_union (content T thiss32) (content T that1))) bool
		(fun _ => Zeq_bool (proj1_sig (size T res3)) (Z.add (proj1_sig (size T thiss32)) (proj1_sig (size T that1))) )
		(fun _ => false ))
	bool
	(fun _ => negb (propInBool ((that1 = Nil_construct T))) || propInBool ((res3 = thiss32)) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold plus_plus__rt10_type.


Equations plus_plus_ (T: Type) (thiss32: List T) (that1: List T) : plus_plus__rt10_type T thiss32 that1 := 
	plus_plus_ T thiss32 that1 by rec ignore_termination lt :=
	plus_plus_ T thiss32 that1 := match thiss32 with
	| Nil_construct _ => that1
	| Cons_construct _ x2 xs => Cons_construct T x2 (proj1_sig (plus_plus_ T xs that1))
	end.

Hint Unfold plus_plus__comp_proj.

Solve Obligations with (repeat t443).
Fail Next Obligation.

Ltac rwrtTac_A180 := match goal with 
	| [ H1492: context[plus_plus_ ?T ?thiss32 ?that1] |- _ ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
	| [  |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			poseNew (Mark (T,thiss32,that1) "unfolding plus_plus__equation")
end.

Ltac rwrtTac_B180 := match goal with 
	| [ H1492: context[plus_plus_ ?T ?thiss32 ?that1], H2492: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- _ ] => 
			let U180 := (fresh "U") in (poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			pose proof (plus_plus__equation_1 T thiss32 that1) as U180;
			rewrite U180 in *)
	| [ H2492: Marked (?T,?thiss32,?that1) "unfolding plus_plus__equation" |- context[plus_plus_ ?T ?thiss32 ?that1] ] => 
			let U180 := (fresh "U") in (poseNew (Mark (T,thiss32,that1) "unfolded plus_plus__equation");
			pose proof (plus_plus__equation_1 T thiss32 that1) as U180;
			rewrite U180 in *)
end.

Ltac rwrtTac180 := rwrtTac179; repeat rwrtTac_A180; repeat rwrtTac_B180.

Ltac t444 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac180 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t444.

(***********************
  End of ++
 ***********************)

(***********************
  Start of -
 ***********************)


Definition minus__rt2_type (T: Type) (thiss33: List T) (e: T) : Type :=
{res4: List T | (ifthenelse (Z.leb (proj1_sig (size T res4)) (proj1_sig (size T thiss33))) bool
	(fun _ => set_equality (content T res4) (set_difference (content T thiss33) (set_union (@set_empty T) (set_singleton e))) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold minus__rt2_type.


Equations minus_ (T: Type) (thiss33: List T) (e: T) : minus__rt2_type T thiss33 e := 
	minus_ T thiss33 e by rec ignore_termination lt :=
	minus_ T thiss33 e := match thiss33 with
	| Cons_construct _ h14 t151 => 
			ifthenelse (propInBool ((e = h14))) (List T)
				(fun _ => proj1_sig (minus_ T t151 e) )
				(fun _ => Cons_construct T h14 (proj1_sig (minus_ T t151 e)) )
	| Nil_construct _ => Nil_construct T
	end.

Hint Unfold minus__comp_proj.

Solve Obligations with (repeat t444).
Fail Next Obligation.

Ltac rwrtTac_A181 := match goal with 
	| [ H1493: context[minus_ ?T ?thiss33 ?e] |- _ ] => 
			poseNew (Mark (T,thiss33,e) "unfolding minus__equation")
	| [  |- context[minus_ ?T ?thiss33 ?e] ] => 
			poseNew (Mark (T,thiss33,e) "unfolding minus__equation")
end.

Ltac rwrtTac_B181 := match goal with 
	| [ H1493: context[minus_ ?T ?thiss33 ?e], H2493: Marked (?T,?thiss33,?e) "unfolding minus__equation" |- _ ] => 
			let U181 := (fresh "U") in (poseNew (Mark (T,thiss33,e) "unfolded minus__equation");
			pose proof (minus__equation_1 T thiss33 e) as U181;
			rewrite U181 in *)
	| [ H2493: Marked (?T,?thiss33,?e) "unfolding minus__equation" |- context[minus_ ?T ?thiss33 ?e] ] => 
			let U181 := (fresh "U") in (poseNew (Mark (T,thiss33,e) "unfolded minus__equation");
			pose proof (minus__equation_1 T thiss33 e) as U181;
			rewrite U181 in *)
end.

Ltac rwrtTac181 := rwrtTac180; repeat rwrtTac_A181; repeat rwrtTac_B181.

Ltac t445 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac181 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t445.

(***********************
  End of -
 ***********************)

(***********************
  Start of --
 ***********************)


Definition substract__rt1_type (T: Type) (thiss34: List T) (that2: List T) : Type :=
{res5: List T | (ifthenelse (Z.leb (proj1_sig (size T res5)) (proj1_sig (size T thiss34))) bool
	(fun _ => set_equality (content T res5) (set_difference (content T thiss34) (content T that2)) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold substract__rt1_type.


Equations substract_ (T: Type) (thiss34: List T) (that2: List T) : substract__rt1_type T thiss34 that2 := 
	substract_ T thiss34 that2 by rec ignore_termination lt :=
	substract_ T thiss34 that2 := match thiss34 with
	| Cons_construct _ h15 t159 => 
			ifthenelse (proj1_sig (contains T that2 h15)) (List T)
				(fun _ => proj1_sig (substract_ T t159 that2) )
				(fun _ => Cons_construct T h15 (proj1_sig (substract_ T t159 that2)) )
	| Nil_construct _ => Nil_construct T
	end.

Hint Unfold substract__comp_proj.

Solve Obligations with (repeat t445).
Fail Next Obligation.

Ltac rwrtTac_A182 := match goal with 
	| [ H1494: context[substract_ ?T ?thiss34 ?that2] |- _ ] => 
			poseNew (Mark (T,thiss34,that2) "unfolding substract__equation")
	| [  |- context[substract_ ?T ?thiss34 ?that2] ] => 
			poseNew (Mark (T,thiss34,that2) "unfolding substract__equation")
end.

Ltac rwrtTac_B182 := match goal with 
	| [ H1494: context[substract_ ?T ?thiss34 ?that2], H2494: Marked (?T,?thiss34,?that2) "unfolding substract__equation" |- _ ] => 
			let U182 := (fresh "U") in (poseNew (Mark (T,thiss34,that2) "unfolded substract__equation");
			pose proof (substract__equation_1 T thiss34 that2) as U182;
			rewrite U182 in *)
	| [ H2494: Marked (?T,?thiss34,?that2) "unfolding substract__equation" |- context[substract_ ?T ?thiss34 ?that2] ] => 
			let U182 := (fresh "U") in (poseNew (Mark (T,thiss34,that2) "unfolded substract__equation");
			pose proof (substract__equation_1 T thiss34 that2) as U182;
			rewrite U182 in *)
end.

Ltac rwrtTac182 := rwrtTac181; repeat rwrtTac_A182; repeat rwrtTac_B182.

Ltac t446 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac182 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t446.

(***********************
  End of --
 ***********************)

(***********************
  Start of :+
 ***********************)


Definition snoc__rt4_type (T: Type) (thiss35: List T) (t166: T) : Type :=
{res6: List T | (magic bool = true)}.

Fail Next Obligation.

Hint Unfold snoc__rt4_type.


Equations snoc_ (T: Type) (thiss35: List T) (t166: T) : snoc__rt4_type T thiss35 t166 := 
	snoc_ T thiss35 t166 by rec ignore_termination lt :=
	snoc_ T thiss35 t166 := match thiss35 with
	| Nil_construct _ => Cons_construct T t166 thiss35
	| Cons_construct _ x3 xs1 => Cons_construct T x3 (proj1_sig (snoc_ T xs1 t166))
	end.

Hint Unfold snoc__comp_proj.

Solve Obligations with (repeat t446).
Fail Next Obligation.

Ltac rwrtTac_A183 := match goal with 
	| [ H1495: context[snoc_ ?T ?thiss35 ?t166] |- _ ] => 
			poseNew (Mark (T,thiss35,t166) "unfolding snoc__equation")
	| [  |- context[snoc_ ?T ?thiss35 ?t166] ] => 
			poseNew (Mark (T,thiss35,t166) "unfolding snoc__equation")
end.

Ltac rwrtTac_B183 := match goal with 
	| [ H1495: context[snoc_ ?T ?thiss35 ?t166], H2495: Marked (?T,?thiss35,?t166) "unfolding snoc__equation" |- _ ] => 
			let U183 := (fresh "U") in (poseNew (Mark (T,thiss35,t166) "unfolded snoc__equation");
			pose proof (snoc__equation_1 T thiss35 t166) as U183;
			rewrite U183 in *)
	| [ H2495: Marked (?T,?thiss35,?t166) "unfolding snoc__equation" |- context[snoc_ ?T ?thiss35 ?t166] ] => 
			let U183 := (fresh "U") in (poseNew (Mark (T,thiss35,t166) "unfolded snoc__equation");
			pose proof (snoc__equation_1 T thiss35 t166) as U183;
			rewrite U183 in *)
end.

Ltac rwrtTac183 := rwrtTac182; repeat rwrtTac_A183; repeat rwrtTac_B183.

Ltac t447 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac183 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t447.

(***********************
  End of :+
 ***********************)

(***********************
  Start of chunk0
 ***********************)


Definition contractHyp281_type (T: Type) (thiss36: List T) (s: Z) (l: Z) (acc: Z) (res7: List (List T)) (s0: Z) : Type :=
(ifthenelse (Z.gtb s (0)%Z) bool
	(fun _ => Z.geb s0 (0)%Z )
	(fun _ => false ) = true).

Fail Next Obligation.

Hint Unfold contractHyp281_type.


Definition chunk0_rt2_type (T: Type) (thiss36: List T) (s: Z) (l: Z) (acc: Z) (res7: List (List T)) (s0: Z) (contractHyp281: contractHyp281_type T thiss36 s l acc res7 s0) : Type :=
List (List T).

Fail Next Obligation.

Hint Unfold chunk0_rt2_type.


Equations chunk0 (T: Type) (thiss36: List T) (s: Z) (l: Z) (acc: Z) (res7: List (List T)) (s0: Z) (contractHyp281: contractHyp281_type T thiss36 s l acc res7 s0) : chunk0_rt2_type T thiss36 s l acc res7 s0 contractHyp281 := 
	chunk0 T thiss36 s l acc res7 s0 contractHyp281 by rec ignore_termination lt :=
	chunk0 T thiss36 s l acc res7 s0 contractHyp281 := match l with
	| Nil_construct _ => 
			ifthenelse (Z.gtb (proj1_sig (size T acc)) (0)%Z) (List (List T))
				(fun _ => proj1_sig (snoc_ (List T) res7 acc) )
				(fun _ => res7 )
	| Cons_construct _ h16 t174 => 
			ifthenelse (Zeq_bool s0 (0)%Z) (List (List T))
				(fun _ => chunk0 T thiss36 s t174 (Cons_construct T h16 (Nil_construct T)) (proj1_sig (snoc_ (List T) res7 acc)) (Z.sub s (1)%Z) _ )
				(fun _ => chunk0 T thiss36 s t174 (proj1_sig (snoc_ T acc h16)) res7 (Z.sub s0 (1)%Z) _ )
	end.

Hint Unfold chunk0_comp_proj.

Solve Obligations with (repeat t447).
Fail Next Obligation.

Ltac rwrtTac_A184 := match goal with 
	| [ H1496: context[chunk0 ?T ?thiss36 ?s ?l ?acc ?res7 ?s0] |- _ ] => 
			poseNew (Mark (T,thiss36,s,l,acc,res7,s0) "unfolding chunk0_equation")
	| [  |- context[chunk0 ?T ?thiss36 ?s ?l ?acc ?res7 ?s0] ] => 
			poseNew (Mark (T,thiss36,s,l,acc,res7,s0) "unfolding chunk0_equation")
end.

Ltac rwrtTac_B184 := match goal with 
	| [ H1496: context[chunk0 ?T ?thiss36 ?s ?l ?acc ?res7 ?s0], H2496: Marked (?T,?thiss36,?s,?l,?acc,?res7,?s0) "unfolding chunk0_equation" |- _ ] => 
			let U184 := (fresh "U") in (poseNew (Mark (T,thiss36,s,l,acc,res7,s0) "unfolded chunk0_equation");
			pose proof (chunk0_equation_1 T thiss36 s l acc res7 s0) as U184;
			rewrite U184 in *)
	| [ H2496: Marked (?T,?thiss36,?s,?l,?acc,?res7,?s0) "unfolding chunk0_equation" |- context[chunk0 ?T ?thiss36 ?s ?l ?acc ?res7 ?s0] ] => 
			let U184 := (fresh "U") in (poseNew (Mark (T,thiss36,s,l,acc,res7,s0) "unfolded chunk0_equation");
			pose proof (chunk0_equation_1 T thiss36 s l acc res7 s0) as U184;
			rewrite U184 in *)
end.

Ltac rwrtTac184 := rwrtTac183; repeat rwrtTac_A184; repeat rwrtTac_B184.

Ltac t448 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac184 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t448.

(***********************
  End of chunk0
 ***********************)

(***********************
  Start of chunks
 ***********************)

Definition chunks (T: Type) (thiss37: List T) (s1: Z) (contractHyp282: (Z.gtb s1 (0)%Z = true)) : List (List T) :=
chunk0 T thiss37 s1 thiss37 (Nil_construct T) (Nil_construct (List T)) s1 _.

Fail Next Obligation.

Hint Unfold chunks: definitions.

(***********************
  End of chunks
 ***********************)

(***********************
  Start of drop
 ***********************)


Definition drop_rt7_type (T: Type) (thiss38: List T) (i: Z) : Type :=
{res8: List T | (ifthenelse (set_subset (content T res8) (content T thiss38)) bool
	(fun _ => Zeq_bool (proj1_sig (size T res8)) (ifthenelse (Z.leb i (0)%Z) Z
		(fun _ => proj1_sig (size T thiss38) )
		(fun _ => ifthenelse (Z.geb i (proj1_sig (size T thiss38))) Z
			(fun _ => (0)%Z )
			(fun _ => Z.sub (proj1_sig (size T thiss38)) i ) )) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold drop_rt7_type.


Equations drop (T: Type) (thiss38: List T) (i: Z) : drop_rt7_type T thiss38 i := 
	drop T thiss38 i by rec ignore_termination lt :=
	drop T thiss38 i := ifthenelse (isNil _ thiss38) (List T)
		(fun _ => Nil_construct T )
		(fun _ => ifthenelse (isCons _ thiss38) (List T)
			(fun _ => ifthenelse (Z.leb i (0)%Z) (List T)
				(fun _ => Cons_construct T (h T thiss38) (t4 T thiss38) )
				(fun _ => proj1_sig (drop T (t4 T thiss38) (Z.sub i (1)%Z)) ) )
			(fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold drop_comp_proj.

Solve Obligations with (repeat t448).
Fail Next Obligation.

Ltac rwrtTac_A185 := match goal with 
	| [ H1497: context[drop ?T ?thiss38 ?i] |- _ ] => 
			poseNew (Mark (T,thiss38,i) "unfolding drop_equation")
	| [  |- context[drop ?T ?thiss38 ?i] ] => 
			poseNew (Mark (T,thiss38,i) "unfolding drop_equation")
end.

Ltac rwrtTac_B185 := match goal with 
	| [ H1497: context[drop ?T ?thiss38 ?i], H2497: Marked (?T,?thiss38,?i) "unfolding drop_equation" |- _ ] => 
			let U185 := (fresh "U") in (poseNew (Mark (T,thiss38,i) "unfolded drop_equation");
			pose proof (drop_equation_1 T thiss38 i) as U185;
			rewrite U185 in *)
	| [ H2497: Marked (?T,?thiss38,?i) "unfolding drop_equation" |- context[drop ?T ?thiss38 ?i] ] => 
			let U185 := (fresh "U") in (poseNew (Mark (T,thiss38,i) "unfolded drop_equation");
			pose proof (drop_equation_1 T thiss38 i) as U185;
			rewrite U185 in *)
end.

Ltac rwrtTac185 := rwrtTac184; repeat rwrtTac_A185; repeat rwrtTac_B185.

Ltac t449 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac185 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t449.

(***********************
  End of drop
 ***********************)

(***********************
  Start of dropWhile
 ***********************)


Definition dropWhile_rt1_type (T: Type) (thiss39: List T) (p7: T -> bool) : Type :=
{res9: List T | (ifthenelse
	(ifthenelse (Z.leb (proj1_sig (size T res9)) (proj1_sig (size T thiss39))) bool
		(fun _ => set_subset (content T res9) (content T thiss39) )
		(fun _ => false ))
	bool
	(fun _ => isEmpty T res9 || negb (p7 (head T res9 _)) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold dropWhile_rt1_type.


Equations dropWhile (T: Type) (thiss39: List T) (p7: T -> bool) : dropWhile_rt1_type T thiss39 p7 := 
	dropWhile T thiss39 p7 by rec ignore_termination lt :=
	dropWhile T thiss39 p7 := ifthenelse
		(ifthenelse (isCons _ thiss39) bool
			(fun _ => p7 (h T thiss39) )
			(fun _ => false ))
		(List T)
		(fun _ => proj1_sig (dropWhile T (t4 T thiss39) p7) )
		(fun _ => thiss39 ).

Hint Unfold dropWhile_comp_proj.

Solve Obligations with (repeat t449).
Fail Next Obligation.

Ltac rwrtTac_A186 := match goal with 
	| [ H1498: context[dropWhile ?T ?thiss39 ?p7] |- _ ] => 
			poseNew (Mark (T,thiss39,p7) "unfolding dropWhile_equation")
	| [  |- context[dropWhile ?T ?thiss39 ?p7] ] => 
			poseNew (Mark (T,thiss39,p7) "unfolding dropWhile_equation")
end.

Ltac rwrtTac_B186 := match goal with 
	| [ H1498: context[dropWhile ?T ?thiss39 ?p7], H2498: Marked (?T,?thiss39,?p7) "unfolding dropWhile_equation" |- _ ] => 
			let U186 := (fresh "U") in (poseNew (Mark (T,thiss39,p7) "unfolded dropWhile_equation");
			pose proof (dropWhile_equation_1 T thiss39 p7) as U186;
			rewrite U186 in *)
	| [ H2498: Marked (?T,?thiss39,?p7) "unfolding dropWhile_equation" |- context[dropWhile ?T ?thiss39 ?p7] ] => 
			let U186 := (fresh "U") in (poseNew (Mark (T,thiss39,p7) "unfolded dropWhile_equation");
			pose proof (dropWhile_equation_1 T thiss39 p7) as U186;
			rewrite U186 in *)
end.

Ltac rwrtTac186 := rwrtTac185; repeat rwrtTac_A186; repeat rwrtTac_B186.

Ltac t450 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac186 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t450.

(***********************
  End of dropWhile
 ***********************)

(***********************
  Start of filter
 ***********************)


Definition filter1_rt5_type (T: Type) (thiss40: List T) (p8: T -> bool) : Type :=
{res10: List T | (ifthenelse
	(ifthenelse (Z.leb (proj1_sig (size T res10)) (proj1_sig (size T thiss40))) bool
		(fun _ => set_subset (content T res10) (content T thiss40) )
		(fun _ => false ))
	bool
	(fun _ => forall1 T res10 p8 )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold filter1_rt5_type.


Equations filter1 (T: Type) (thiss40: List T) (p8: T -> bool) : filter1_rt5_type T thiss40 p8 := 
	filter1 T thiss40 p8 by rec ignore_termination lt :=
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

Solve Obligations with (repeat t450).
Fail Next Obligation.

Ltac rwrtTac_A187 := match goal with 
	| [ H1499: context[filter1 ?T ?thiss40 ?p8] |- _ ] => 
			poseNew (Mark (T,thiss40,p8) "unfolding filter1_equation")
	| [  |- context[filter1 ?T ?thiss40 ?p8] ] => 
			poseNew (Mark (T,thiss40,p8) "unfolding filter1_equation")
end.

Ltac rwrtTac_B187 := match goal with 
	| [ H1499: context[filter1 ?T ?thiss40 ?p8], H2499: Marked (?T,?thiss40,?p8) "unfolding filter1_equation" |- _ ] => 
			let U187 := (fresh "U") in (poseNew (Mark (T,thiss40,p8) "unfolded filter1_equation");
			pose proof (filter1_equation_1 T thiss40 p8) as U187;
			rewrite U187 in *)
	| [ H2499: Marked (?T,?thiss40,?p8) "unfolding filter1_equation" |- context[filter1 ?T ?thiss40 ?p8] ] => 
			let U187 := (fresh "U") in (poseNew (Mark (T,thiss40,p8) "unfolded filter1_equation");
			pose proof (filter1_equation_1 T thiss40 p8) as U187;
			rewrite U187 in *)
end.

Ltac rwrtTac187 := rwrtTac186; repeat rwrtTac_A187; repeat rwrtTac_B187.

Ltac t451 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac187 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t451.

(***********************
  End of filter
 ***********************)

(***********************
  Start of count
 ***********************)


Definition count_rt1_type (T: Type) (thiss41: List T) (p9: T -> bool) : Type :=
{x___24: Z | (Zeq_bool x___24 (proj1_sig (size T (proj1_sig (filter1 T thiss41 p9)))) = true)}.

Fail Next Obligation.

Hint Unfold count_rt1_type.


Equations count (T: Type) (thiss41: List T) (p9: T -> bool) : count_rt1_type T thiss41 p9 := 
	count T thiss41 p9 by rec ignore_termination lt :=
	count T thiss41 p9 := match thiss41 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h17 t209 => 
			Z.add (ifthenelse (p9 h17) Z
				(fun _ => (1)%Z )
				(fun _ => (0)%Z )) (proj1_sig (count T t209 p9))
	end.

Hint Unfold count_comp_proj.

Solve Obligations with (repeat t451).
Fail Next Obligation.

Ltac rwrtTac_A188 := match goal with 
	| [ H1500: context[count ?T ?thiss41 ?p9] |- _ ] => 
			poseNew (Mark (T,thiss41,p9) "unfolding count_equation")
	| [  |- context[count ?T ?thiss41 ?p9] ] => 
			poseNew (Mark (T,thiss41,p9) "unfolding count_equation")
end.

Ltac rwrtTac_B188 := match goal with 
	| [ H1500: context[count ?T ?thiss41 ?p9], H2500: Marked (?T,?thiss41,?p9) "unfolding count_equation" |- _ ] => 
			let U188 := (fresh "U") in (poseNew (Mark (T,thiss41,p9) "unfolded count_equation");
			pose proof (count_equation_1 T thiss41 p9) as U188;
			rewrite U188 in *)
	| [ H2500: Marked (?T,?thiss41,?p9) "unfolding count_equation" |- context[count ?T ?thiss41 ?p9] ] => 
			let U188 := (fresh "U") in (poseNew (Mark (T,thiss41,p9) "unfolded count_equation");
			pose proof (count_equation_1 T thiss41 p9) as U188;
			rewrite U188 in *)
end.

Ltac rwrtTac188 := rwrtTac187; repeat rwrtTac_A188; repeat rwrtTac_B188.

Ltac t452 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac188 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t452.

(***********************
  End of count
 ***********************)

(***********************
  Start of filterNot
 ***********************)

Definition filterNot (T: Type) (thiss42: List T) (p10: T -> bool) : {res11: List T | (ifthenelse
	(ifthenelse (Z.leb (proj1_sig (size T res11)) (proj1_sig (size T thiss42))) bool
		(fun _ => set_subset (content T res11) (content T thiss42) )
		(fun _ => false ))
	bool
	(fun _ => forall1 T res11 (fun x___18 => negb (p10 x___18) ) )
	(fun _ => false ) = true)} :=
proj1_sig (filter1 T thiss42 (fun x___17 => negb (p10 x___17) )).

Fail Next Obligation.

Hint Unfold filterNot: definitions.

(***********************
  End of filterNot
 ***********************)

(***********************
  Start of flatten
 ***********************)


Definition flatten_rt2_type (T: Type) (ls: List (List T)) : Type :=
List T.

Fail Next Obligation.

Hint Unfold flatten_rt2_type.


Equations flatten (T: Type) (ls: List (List T)) : flatten_rt2_type T ls := 
	flatten T ls by rec ignore_termination lt :=
	flatten T ls := match ls with
	| Cons_construct _ h18 t224 => proj1_sig (plus_plus_ T h18 (flatten T t224))
	| Nil_construct _ => Nil_construct T
	end.

Hint Unfold flatten_comp_proj.

Solve Obligations with (repeat t452).
Fail Next Obligation.

Ltac rwrtTac_A189 := match goal with 
	| [ H1501: context[flatten ?T ?ls] |- _ ] => 
			poseNew (Mark (T,ls) "unfolding flatten_equation")
	| [  |- context[flatten ?T ?ls] ] => 
			poseNew (Mark (T,ls) "unfolding flatten_equation")
end.

Ltac rwrtTac_B189 := match goal with 
	| [ H1501: context[flatten ?T ?ls], H2501: Marked (?T,?ls) "unfolding flatten_equation" |- _ ] => 
			let U189 := (fresh "U") in (poseNew (Mark (T,ls) "unfolded flatten_equation");
			pose proof (flatten_equation_1 T ls) as U189;
			rewrite U189 in *)
	| [ H2501: Marked (?T,?ls) "unfolding flatten_equation" |- context[flatten ?T ?ls] ] => 
			let U189 := (fresh "U") in (poseNew (Mark (T,ls) "unfolded flatten_equation");
			pose proof (flatten_equation_1 T ls) as U189;
			rewrite U189 in *)
end.

Ltac rwrtTac189 := rwrtTac188; repeat rwrtTac_A189; repeat rwrtTac_B189.

Ltac t453 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac189 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t453.

(***********************
  End of flatten
 ***********************)

(***********************
  Start of init
 ***********************)


Definition contractHyp289_type (T: Type) (thiss43: List T) : Type :=
(negb (isEmpty T thiss43) = true).

Fail Next Obligation.

Hint Unfold contractHyp289_type.


Definition init_rt1_type (T: Type) (thiss43: List T) (contractHyp289: contractHyp289_type T thiss43) : Type :=
{r1: List T | (ifthenelse (Zeq_bool (proj1_sig (size T r1)) (Z.sub (proj1_sig (size T thiss43)) (1)%Z)) bool
	(fun _ => set_subset (content T r1) (content T thiss43) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold init_rt1_type.


Equations init (T: Type) (thiss43: List T) (contractHyp289: contractHyp289_type T thiss43) : init_rt1_type T thiss43 contractHyp289 := 
	init T thiss43 contractHyp289 by rec ignore_termination lt :=
	init T thiss43 contractHyp289 := ifthenelse
		(ifthenelse (isCons _ thiss43) bool
			(fun _ => isNil _ (t4 T thiss43) )
			(fun _ => false ))
		(List T)
		(fun _ => Nil_construct T )
		(fun _ => ifthenelse (isCons _ thiss43) (List T)
			(fun _ => Cons_construct T (h T thiss43) (proj1_sig (init T (t4 T thiss43) _)) )
			(fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold init_comp_proj.

Solve Obligations with (repeat t453).
Fail Next Obligation.

Ltac rwrtTac_A190 := match goal with 
	| [ H1502: context[init ?T ?thiss43] |- _ ] => 
			poseNew (Mark (T,thiss43) "unfolding init_equation")
	| [  |- context[init ?T ?thiss43] ] => 
			poseNew (Mark (T,thiss43) "unfolding init_equation")
end.

Ltac rwrtTac_B190 := match goal with 
	| [ H1502: context[init ?T ?thiss43], H2502: Marked (?T,?thiss43) "unfolding init_equation" |- _ ] => 
			let U190 := (fresh "U") in (poseNew (Mark (T,thiss43) "unfolded init_equation");
			pose proof (init_equation_1 T thiss43) as U190;
			rewrite U190 in *)
	| [ H2502: Marked (?T,?thiss43) "unfolding init_equation" |- context[init ?T ?thiss43] ] => 
			let U190 := (fresh "U") in (poseNew (Mark (T,thiss43) "unfolded init_equation");
			pose proof (init_equation_1 T thiss43) as U190;
			rewrite U190 in *)
end.

Ltac rwrtTac190 := rwrtTac189; repeat rwrtTac_A190; repeat rwrtTac_B190.

Ltac t454 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac190 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t454.

(***********************
  End of init
 ***********************)

(***********************
  Start of insertAtImpl
 ***********************)


Definition contractHyp290_type (T: Type) (thiss44: List T) (pos: Z) (l1: List T) : Type :=
(ifthenelse (Z.leb (0)%Z pos) bool
	(fun _ => Z.leb pos (proj1_sig (size T thiss44)) )
	(fun _ => false ) = true).

Fail Next Obligation.

Hint Unfold contractHyp290_type.


Definition insertAtImpl_rt3_type (T: Type) (thiss44: List T) (pos: Z) (l1: List T) (contractHyp290: contractHyp290_type T thiss44 pos l1) : Type :=
{res12: List T | (ifthenelse (Zeq_bool (proj1_sig (size T res12)) (Z.add (proj1_sig (size T thiss44)) (proj1_sig (size T l1)))) bool
	(fun _ => set_equality (content T res12) (set_union (content T thiss44) (content T l1)) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold insertAtImpl_rt3_type.


Equations insertAtImpl (T: Type) (thiss44: List T) (pos: Z) (l1: List T) (contractHyp290: contractHyp290_type T thiss44 pos l1) : insertAtImpl_rt3_type T thiss44 pos l1 contractHyp290 := 
	insertAtImpl T thiss44 pos l1 contractHyp290 by rec ignore_termination lt :=
	insertAtImpl T thiss44 pos l1 contractHyp290 := ifthenelse (Zeq_bool pos (0)%Z) (List T)
		(fun _ => proj1_sig (plus_plus_ T l1 thiss44) )
		(fun _ => match thiss44 with
		| Cons_construct _ h19 t238 => 
				Cons_construct T h19 (proj1_sig (insertAtImpl T t238 (Z.sub pos (1)%Z) l1 _))
		| Nil_construct _ => l1
		end ).

Hint Unfold insertAtImpl_comp_proj.

Solve Obligations with (repeat t454).
Fail Next Obligation.

Ltac rwrtTac_A191 := match goal with 
	| [ H1503: context[insertAtImpl ?T ?thiss44 ?pos ?l1] |- _ ] => 
			poseNew (Mark (T,thiss44,pos,l1) "unfolding insertAtImpl_equation")
	| [  |- context[insertAtImpl ?T ?thiss44 ?pos ?l1] ] => 
			poseNew (Mark (T,thiss44,pos,l1) "unfolding insertAtImpl_equation")
end.

Ltac rwrtTac_B191 := match goal with 
	| [ H1503: context[insertAtImpl ?T ?thiss44 ?pos ?l1], H2503: Marked (?T,?thiss44,?pos,?l1) "unfolding insertAtImpl_equation" |- _ ] => 
			let U191 := (fresh "U") in (poseNew (Mark (T,thiss44,pos,l1) "unfolded insertAtImpl_equation");
			pose proof (insertAtImpl_equation_1 T thiss44 pos l1) as U191;
			rewrite U191 in *)
	| [ H2503: Marked (?T,?thiss44,?pos,?l1) "unfolding insertAtImpl_equation" |- context[insertAtImpl ?T ?thiss44 ?pos ?l1] ] => 
			let U191 := (fresh "U") in (poseNew (Mark (T,thiss44,pos,l1) "unfolded insertAtImpl_equation");
			pose proof (insertAtImpl_equation_1 T thiss44 pos l1) as U191;
			rewrite U191 in *)
end.

Ltac rwrtTac191 := rwrtTac190; repeat rwrtTac_A191; repeat rwrtTac_B191.

Ltac t455 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac191 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t455.

(***********************
  End of insertAtImpl
 ***********************)

(***********************
  Start of insertAt
 ***********************)

Definition insertAt (T: Type) (thiss45: List T) (pos1: Z) (l2: List T) (contractHyp291: (ifthenelse (Z.leb (Z.opp pos1) (proj1_sig (size T thiss45))) bool
	(fun _ => Z.leb pos1 (proj1_sig (size T thiss45)) )
	(fun _ => false ) = true)) : {res13: List T | (ifthenelse (Zeq_bool (proj1_sig (size T res13)) (Z.add (proj1_sig (size T thiss45)) (proj1_sig (size T l2)))) bool
	(fun _ => set_equality (content T res13) (set_union (content T thiss45) (content T l2)) )
	(fun _ => false ) = true)} :=
ifthenelse (Z.ltb pos1 (0)%Z) (List T)
	(fun _ => proj1_sig (insertAtImpl T thiss45 (Z.add (proj1_sig (size T thiss45)) pos1) l2 _) )
	(fun _ => proj1_sig (insertAtImpl T thiss45 pos1 l2 _) ).

Fail Next Obligation.

Hint Unfold insertAt: definitions.

(***********************
  End of insertAt
 ***********************)

(***********************
  Start of insertAt
 ***********************)

Definition insertAt1 (T: Type) (thiss46: List T) (pos2: Z) (e1: T) (contractHyp292: (ifthenelse (Z.leb (Z.opp pos2) (proj1_sig (size T thiss46))) bool
	(fun _ => Z.leb pos2 (proj1_sig (size T thiss46)) )
	(fun _ => false ) = true)) : {res14: List T | (ifthenelse (Zeq_bool (proj1_sig (size T res14)) (Z.add (proj1_sig (size T thiss46)) (1)%Z)) bool
	(fun _ => set_equality (content T res14) (set_union (content T thiss46) (set_union (@set_empty T) (set_singleton e1))) )
	(fun _ => false ) = true)} :=
proj1_sig (insertAt T thiss46 pos2 (Cons_construct T e1 (Nil_construct T)) _).

Fail Next Obligation.

Hint Unfold insertAt1: definitions.

(***********************
  End of insertAt
 ***********************)

(***********************
  Start of length
 ***********************)

Definition length (T: Type) (thiss47: List T) : Z :=
proj1_sig (size T thiss47).

Fail Next Obligation.

Hint Unfold length: definitions.

(***********************
  End of length
 ***********************)

(***********************
  Start of map
 ***********************)


Definition map1_rt2_type (T: Type) (R: Type) (thiss48: List T) (f7: T -> R) : Type :=
{x___9: List R | (Zeq_bool (proj1_sig (size R x___9)) (proj1_sig (size T thiss48)) = true)}.

Fail Next Obligation.

Hint Unfold map1_rt2_type.


Equations map1 (T: Type) (R: Type) (thiss48: List T) (f7: T -> R) : map1_rt2_type T R thiss48 f7 := 
	map1 T R thiss48 f7 by rec ignore_termination lt :=
	map1 T R thiss48 f7 := match thiss48 with
	| Nil_construct _ => Nil_construct R
	| Cons_construct _ h20 t262 => 
			let x___8 := (f7 h20) in (cons_ R (proj1_sig (map1 T R t262 f7)) x___8)
	end.

Hint Unfold map1_comp_proj.

Solve Obligations with (repeat t455).
Fail Next Obligation.

Ltac rwrtTac_A192 := match goal with 
	| [ H1504: context[map1 ?T ?R ?thiss48 ?f7] |- _ ] => 
			poseNew (Mark (T,R,thiss48,f7) "unfolding map1_equation")
	| [  |- context[map1 ?T ?R ?thiss48 ?f7] ] => 
			poseNew (Mark (T,R,thiss48,f7) "unfolding map1_equation")
end.

Ltac rwrtTac_B192 := match goal with 
	| [ H1504: context[map1 ?T ?R ?thiss48 ?f7], H2504: Marked (?T,?R,?thiss48,?f7) "unfolding map1_equation" |- _ ] => 
			let U192 := (fresh "U") in (poseNew (Mark (T,R,thiss48,f7) "unfolded map1_equation");
			pose proof (map1_equation_1 T R thiss48 f7) as U192;
			rewrite U192 in *)
	| [ H2504: Marked (?T,?R,?thiss48,?f7) "unfolding map1_equation" |- context[map1 ?T ?R ?thiss48 ?f7] ] => 
			let U192 := (fresh "U") in (poseNew (Mark (T,R,thiss48,f7) "unfolded map1_equation");
			pose proof (map1_equation_1 T R thiss48 f7) as U192;
			rewrite U192 in *)
end.

Ltac rwrtTac192 := rwrtTac191; repeat rwrtTac_A192; repeat rwrtTac_B192.

Ltac t456 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac192 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t456.

(***********************
  End of map
 ***********************)

(***********************
  Start of flatMap
 ***********************)

Definition flatMap1 (T: Type) (R: Type) (thiss49: List T) (f8: T -> (List R)) : List R :=
flatten R (proj1_sig (map1 T (List R) thiss49 f8)).

Fail Next Obligation.

Hint Unfold flatMap1: definitions.

(***********************
  End of flatMap
 ***********************)

(***********************
  Start of padTo
 ***********************)


Definition padTo_rt1_type (T: Type) (thiss50: List T) (s2: Z) (e2: T) : Type :=
{res15: List T | (ifthenelse (Z.leb s2 (proj1_sig (size T thiss50))) bool
	(fun _ => propInBool ((res15 = thiss50)) )
	(fun _ => ifthenelse (Zeq_bool (proj1_sig (size T res15)) s2) bool
		(fun _ => set_equality (content T res15) (set_union (content T thiss50) (set_union (@set_empty T) (set_singleton e2))) )
		(fun _ => false ) ) = true)}.

Fail Next Obligation.

Hint Unfold padTo_rt1_type.


Equations padTo (T: Type) (thiss50: List T) (s2: Z) (e2: T) : padTo_rt1_type T thiss50 s2 e2 := 
	padTo T thiss50 s2 e2 by rec ignore_termination lt :=
	padTo T thiss50 s2 e2 := ifthenelse (Z.leb s2 (0)%Z) (List T)
		(fun _ => thiss50 )
		(fun _ => ifthenelse (isNil _ thiss50) (List T)
			(fun _ => Cons_construct T e2 (proj1_sig (padTo T (Nil_construct T) (Z.sub s2 (1)%Z) e2)) )
			(fun _ => ifthenelse (isCons _ thiss50) (List T)
				(fun _ => Cons_construct T (h T thiss50) (proj1_sig (padTo T (t4 T thiss50) (Z.sub s2 (1)%Z) e2)) )
				(fun _ => let contradiction: False := _ in match contradiction with end ) ) ).

Hint Unfold padTo_comp_proj.

Solve Obligations with (repeat t456).
Fail Next Obligation.

Ltac rwrtTac_A193 := match goal with 
	| [ H1505: context[padTo ?T ?thiss50 ?s2 ?e2] |- _ ] => 
			poseNew (Mark (T,thiss50,s2,e2) "unfolding padTo_equation")
	| [  |- context[padTo ?T ?thiss50 ?s2 ?e2] ] => 
			poseNew (Mark (T,thiss50,s2,e2) "unfolding padTo_equation")
end.

Ltac rwrtTac_B193 := match goal with 
	| [ H1505: context[padTo ?T ?thiss50 ?s2 ?e2], H2505: Marked (?T,?thiss50,?s2,?e2) "unfolding padTo_equation" |- _ ] => 
			let U193 := (fresh "U") in (poseNew (Mark (T,thiss50,s2,e2) "unfolded padTo_equation");
			pose proof (padTo_equation_1 T thiss50 s2 e2) as U193;
			rewrite U193 in *)
	| [ H2505: Marked (?T,?thiss50,?s2,?e2) "unfolding padTo_equation" |- context[padTo ?T ?thiss50 ?s2 ?e2] ] => 
			let U193 := (fresh "U") in (poseNew (Mark (T,thiss50,s2,e2) "unfolded padTo_equation");
			pose proof (padTo_equation_1 T thiss50 s2 e2) as U193;
			rewrite U193 in *)
end.

Ltac rwrtTac193 := rwrtTac192; repeat rwrtTac_A193; repeat rwrtTac_B193.

Ltac t457 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac193 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t457.

(***********************
  End of padTo
 ***********************)

(***********************
  Start of partition
 ***********************)


Definition partition_rt1_type (T: Type) (thiss51: List T) (p11: T -> bool) : Type :=
{res16: ((List T) * (List T))%type | (ifthenelse (propInBool ((fst res16 = proj1_sig (filter1 T thiss51 p11)))) bool
	(fun _ => propInBool ((snd res16 = proj1_sig (filterNot T thiss51 p11))) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold partition_rt1_type.


Equations partition (T: Type) (thiss51: List T) (p11: T -> bool) : partition_rt1_type T thiss51 p11 := 
	partition T thiss51 p11 by rec ignore_termination lt :=
	partition T thiss51 p11 := match thiss51 with
	| Nil_construct _ => (Nil_construct T,Nil_construct T)
	| Cons_construct _ h21 t285 => 
			let x___19 := ((fst (proj1_sig (partition T t285 p11)),snd (proj1_sig (partition T t285 p11)))) in (let l2 := (snd x___19) in (ifthenelse (p11 h21) (((List T) * (List T))%type)
				(fun _ => (cons_ T (fst x___19) h21,l2) )
				(fun _ => (fst x___19,cons_ T l2 h21) )))
	end.

Hint Unfold partition_comp_proj.

Solve Obligations with (repeat t457).
Fail Next Obligation.

Ltac rwrtTac_A194 := match goal with 
	| [ H1506: context[partition ?T ?thiss51 ?p11] |- _ ] => 
			poseNew (Mark (T,thiss51,p11) "unfolding partition_equation")
	| [  |- context[partition ?T ?thiss51 ?p11] ] => 
			poseNew (Mark (T,thiss51,p11) "unfolding partition_equation")
end.

Ltac rwrtTac_B194 := match goal with 
	| [ H1506: context[partition ?T ?thiss51 ?p11], H2506: Marked (?T,?thiss51,?p11) "unfolding partition_equation" |- _ ] => 
			let U194 := (fresh "U") in (poseNew (Mark (T,thiss51,p11) "unfolded partition_equation");
			pose proof (partition_equation_1 T thiss51 p11) as U194;
			rewrite U194 in *)
	| [ H2506: Marked (?T,?thiss51,?p11) "unfolding partition_equation" |- context[partition ?T ?thiss51 ?p11] ] => 
			let U194 := (fresh "U") in (poseNew (Mark (T,thiss51,p11) "unfolded partition_equation");
			pose proof (partition_equation_1 T thiss51 p11) as U194;
			rewrite U194 in *)
end.

Ltac rwrtTac194 := rwrtTac193; repeat rwrtTac_A194; repeat rwrtTac_B194.

Ltac t458 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac194 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t458.

(***********************
  End of partition
 ***********************)

(***********************
  Start of replace
 ***********************)


Definition replace_rt1_type (T: Type) (thiss52: List T) (from: T) (to: T) : Type :=
{res17: List T | (ifthenelse (Zeq_bool (proj1_sig (size T res17)) (proj1_sig (size T thiss52))) bool
	(fun _ => set_equality (content T res17) (set_union (set_difference (content T thiss52) (set_union (@set_empty T) (set_singleton from))) (ifthenelse (set_elem_of from (content T thiss52)) (set (T))
		(fun _ => set_union (@set_empty T) (set_singleton to) )
		(fun _ => @set_empty T ))) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold replace_rt1_type.


Equations replace (T: Type) (thiss52: List T) (from: T) (to: T) : replace_rt1_type T thiss52 from to := 
	replace T thiss52 from to by rec ignore_termination lt :=
	replace T thiss52 from to := match thiss52 with
	| Nil_construct _ => Nil_construct T
	| Cons_construct _ h22 t292 => 
			let r2 := (proj1_sig (replace T t292 from to)) in (ifthenelse (propInBool ((h22 = from))) (List T)
				(fun _ => Cons_construct T to r2 )
				(fun _ => Cons_construct T h22 r2 ))
	end.

Hint Unfold replace_comp_proj.

Solve Obligations with (repeat t458).
Fail Next Obligation.

Ltac rwrtTac_A195 := match goal with 
	| [ H1507: context[replace ?T ?thiss52 ?from ?to] |- _ ] => 
			poseNew (Mark (T,thiss52,from,to) "unfolding replace_equation")
	| [  |- context[replace ?T ?thiss52 ?from ?to] ] => 
			poseNew (Mark (T,thiss52,from,to) "unfolding replace_equation")
end.

Ltac rwrtTac_B195 := match goal with 
	| [ H1507: context[replace ?T ?thiss52 ?from ?to], H2507: Marked (?T,?thiss52,?from,?to) "unfolding replace_equation" |- _ ] => 
			let U195 := (fresh "U") in (poseNew (Mark (T,thiss52,from,to) "unfolded replace_equation");
			pose proof (replace_equation_1 T thiss52 from to) as U195;
			rewrite U195 in *)
	| [ H2507: Marked (?T,?thiss52,?from,?to) "unfolding replace_equation" |- context[replace ?T ?thiss52 ?from ?to] ] => 
			let U195 := (fresh "U") in (poseNew (Mark (T,thiss52,from,to) "unfolded replace_equation");
			pose proof (replace_equation_1 T thiss52 from to) as U195;
			rewrite U195 in *)
end.

Ltac rwrtTac195 := rwrtTac194; repeat rwrtTac_A195; repeat rwrtTac_B195.

Ltac t459 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac195 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t459.

(***********************
  End of replace
 ***********************)

(***********************
  Start of replaceAtImpl
 ***********************)


Definition contractHyp299_type (T: Type) (thiss53: List T) (pos3: List T) (l3: List T) : Type :=
(ifthenelse (Z.leb (0)%Z pos3) bool
	(fun _ => Z.leb pos3 (proj1_sig (size T thiss53)) )
	(fun _ => false ) = true).

Fail Next Obligation.

Hint Unfold contractHyp299_type.


Definition replaceAtImpl_rt2_type (T: Type) (thiss53: List T) (pos3: List T) (l3: List T) (contractHyp299: contractHyp299_type T thiss53 pos3 l3) : Type :=
{res18: List T | (set_subset (content T res18) (set_union (content T l3) (content T thiss53)) = true)}.

Fail Next Obligation.

Hint Unfold replaceAtImpl_rt2_type.


Equations replaceAtImpl (T: Type) (thiss53: List T) (pos3: List T) (l3: List T) (contractHyp299: contractHyp299_type T thiss53 pos3 l3) : replaceAtImpl_rt2_type T thiss53 pos3 l3 contractHyp299 := 
	replaceAtImpl T thiss53 pos3 l3 contractHyp299 by rec ignore_termination lt :=
	replaceAtImpl T thiss53 pos3 l3 contractHyp299 := ifthenelse (Zeq_bool pos3 (0)%Z) (List T)
		(fun _ => proj1_sig (plus_plus_ T l3 (proj1_sig (drop T thiss53 (proj1_sig (size T l3))))) )
		(fun _ => match thiss53 with
		| Cons_construct _ h23 t301 => 
				Cons_construct T h23 (proj1_sig (replaceAtImpl T t301 (Z.sub pos3 (1)%Z) l3 _))
		| Nil_construct _ => l3
		end ).

Hint Unfold replaceAtImpl_comp_proj.

Solve Obligations with (repeat t459).
Fail Next Obligation.

Ltac rwrtTac_A196 := match goal with 
	| [ H1508: context[replaceAtImpl ?T ?thiss53 ?pos3 ?l3] |- _ ] => 
			poseNew (Mark (T,thiss53,pos3,l3) "unfolding replaceAtImpl_equation")
	| [  |- context[replaceAtImpl ?T ?thiss53 ?pos3 ?l3] ] => 
			poseNew (Mark (T,thiss53,pos3,l3) "unfolding replaceAtImpl_equation")
end.

Ltac rwrtTac_B196 := match goal with 
	| [ H1508: context[replaceAtImpl ?T ?thiss53 ?pos3 ?l3], H2508: Marked (?T,?thiss53,?pos3,?l3) "unfolding replaceAtImpl_equation" |- _ ] => 
			let U196 := (fresh "U") in (poseNew (Mark (T,thiss53,pos3,l3) "unfolded replaceAtImpl_equation");
			pose proof (replaceAtImpl_equation_1 T thiss53 pos3 l3) as U196;
			rewrite U196 in *)
	| [ H2508: Marked (?T,?thiss53,?pos3,?l3) "unfolding replaceAtImpl_equation" |- context[replaceAtImpl ?T ?thiss53 ?pos3 ?l3] ] => 
			let U196 := (fresh "U") in (poseNew (Mark (T,thiss53,pos3,l3) "unfolded replaceAtImpl_equation");
			pose proof (replaceAtImpl_equation_1 T thiss53 pos3 l3) as U196;
			rewrite U196 in *)
end.

Ltac rwrtTac196 := rwrtTac195; repeat rwrtTac_A196; repeat rwrtTac_B196.

Ltac t460 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac196 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t460.

(***********************
  End of replaceAtImpl
 ***********************)

(***********************
  Start of replaceAt
 ***********************)

Definition replaceAt (T: Type) (thiss54: List T) (pos4: Z) (l4: List T) (contractHyp300: (ifthenelse (Z.leb (Z.opp pos4) (proj1_sig (size T thiss54))) bool
	(fun _ => Z.leb pos4 (proj1_sig (size T thiss54)) )
	(fun _ => false ) = true)) : {res19: List T | (set_subset (content T res19) (set_union (content T l4) (content T thiss54)) = true)} :=
ifthenelse (Z.ltb pos4 (0)%Z) (List T)
	(fun _ => proj1_sig (replaceAtImpl T thiss54 (Z.add (proj1_sig (size T thiss54)) pos4) l4 _) )
	(fun _ => proj1_sig (replaceAtImpl T thiss54 pos4 l4 _) ).

Fail Next Obligation.

Hint Unfold replaceAt: definitions.

(***********************
  End of replaceAt
 ***********************)

(***********************
  Start of reverse
 ***********************)


Definition reverse_rt1_type (T: Type) (thiss55: List T) : Type :=
{res20: List T | (ifthenelse (Zeq_bool (proj1_sig (size T res20)) (proj1_sig (size T thiss55))) bool
	(fun _ => set_equality (content T res20) (content T thiss55) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold reverse_rt1_type.


Equations reverse (T: Type) (thiss55: List T) : reverse_rt1_type T thiss55 := 
	reverse T thiss55 by rec ignore_termination lt :=
	reverse T thiss55 := match thiss55 with
	| Nil_construct _ => thiss55
	| Cons_construct _ x4 xs2 => proj1_sig (snoc_ T (proj1_sig (reverse T xs2)) x4)
	end.

Hint Unfold reverse_comp_proj.

Solve Obligations with (repeat t460).
Fail Next Obligation.

Ltac rwrtTac_A197 := match goal with 
	| [ H1509: context[reverse ?T ?thiss55] |- _ ] => 
			poseNew (Mark (T,thiss55) "unfolding reverse_equation")
	| [  |- context[reverse ?T ?thiss55] ] => 
			poseNew (Mark (T,thiss55) "unfolding reverse_equation")
end.

Ltac rwrtTac_B197 := match goal with 
	| [ H1509: context[reverse ?T ?thiss55], H2509: Marked (?T,?thiss55) "unfolding reverse_equation" |- _ ] => 
			let U197 := (fresh "U") in (poseNew (Mark (T,thiss55) "unfolded reverse_equation");
			pose proof (reverse_equation_1 T thiss55) as U197;
			rewrite U197 in *)
	| [ H2509: Marked (?T,?thiss55) "unfolding reverse_equation" |- context[reverse ?T ?thiss55] ] => 
			let U197 := (fresh "U") in (poseNew (Mark (T,thiss55) "unfolded reverse_equation");
			pose proof (reverse_equation_1 T thiss55) as U197;
			rewrite U197 in *)
end.

Ltac rwrtTac197 := rwrtTac196; repeat rwrtTac_A197; repeat rwrtTac_B197.

Ltac t461 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac197 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t461.

(***********************
  End of reverse
 ***********************)

(***********************
  Start of tail
 ***********************)

Definition tail (T: Type) (thiss56: List T) (contractHyp302: (negb (propInBool ((thiss56 = Nil_construct T))) = true)) : List T :=
ifthenelse (isCons _ thiss56) (List T)
	(fun _ => t4 T thiss56 )
	(fun _ => let contradiction: False := _ in match contradiction with end ).

Fail Next Obligation.

Hint Unfold tail: definitions.

(***********************
  End of tail
 ***********************)

(***********************
  Start of apply
 ***********************)


Definition contractHyp303_type (T: Type) (thiss57: List T) (index: Z) : Type :=
(ifthenelse (Z.leb (0)%Z index) bool
	(fun _ => Z.ltb index (proj1_sig (size T thiss57)) )
	(fun _ => false ) = true).

Fail Next Obligation.

Hint Unfold contractHyp303_type.


Definition apply_rt1_type (T: Type) (thiss57: List T) (index: Z) (contractHyp303: contractHyp303_type T thiss57 index) : Type :=
T.

Fail Next Obligation.

Hint Unfold apply_rt1_type.


Equations apply (T: Type) (thiss57: List T) (index: Z) (contractHyp303: contractHyp303_type T thiss57 index) : apply_rt1_type T thiss57 index contractHyp303 := 
	apply T thiss57 index contractHyp303 by rec ignore_termination lt :=
	apply T thiss57 index contractHyp303 := ifthenelse (Zeq_bool index (0)%Z) T
		(fun _ => head T thiss57 _ )
		(fun _ => apply T (tail T thiss57 _) (Z.sub index (1)%Z) _ ).

Hint Unfold apply_comp_proj.

Solve Obligations with (repeat t461).
Fail Next Obligation.

Ltac rwrtTac_A198 := match goal with 
	| [ H1510: context[apply ?T ?thiss57 ?index] |- _ ] => 
			poseNew (Mark (T,thiss57,index) "unfolding apply_equation")
	| [  |- context[apply ?T ?thiss57 ?index] ] => 
			poseNew (Mark (T,thiss57,index) "unfolding apply_equation")
end.

Ltac rwrtTac_B198 := match goal with 
	| [ H1510: context[apply ?T ?thiss57 ?index], H2510: Marked (?T,?thiss57,?index) "unfolding apply_equation" |- _ ] => 
			let U198 := (fresh "U") in (poseNew (Mark (T,thiss57,index) "unfolded apply_equation");
			pose proof (apply_equation_1 T thiss57 index) as U198;
			rewrite U198 in *)
	| [ H2510: Marked (?T,?thiss57,?index) "unfolding apply_equation" |- context[apply ?T ?thiss57 ?index] ] => 
			let U198 := (fresh "U") in (poseNew (Mark (T,thiss57,index) "unfolded apply_equation");
			pose proof (apply_equation_1 T thiss57 index) as U198;
			rewrite U198 in *)
end.

Ltac rwrtTac198 := rwrtTac197; repeat rwrtTac_A198; repeat rwrtTac_B198.

Ltac t462 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac198 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t462.

(***********************
  End of apply
 ***********************)

(***********************
  Start of split
 ***********************)


Definition split_rt2_type (T: Type) (thiss58: List T) (seps: List T) : Type :=
List (List T).

Fail Next Obligation.

Hint Unfold split_rt2_type.


Equations split (T: Type) (thiss58: List T) (seps: List T) : split_rt2_type T thiss58 seps := 
	split T thiss58 seps by rec ignore_termination lt :=
	split T thiss58 seps := match thiss58 with
	| Cons_construct _ h24 t331 => 
			ifthenelse (proj1_sig (contains T seps h24)) (List (List T))
				(fun _ => Cons_construct (List T) (Nil_construct T) (split T t331 seps) )
				(fun _ => let r3 := (split T t331 seps) in (Cons_construct (List T) (Cons_construct T h24 (head (List T) r3 _)) (tail (List T) r3 _)) )
	| Nil_construct _ => 
			Cons_construct (List T) (Nil_construct T) (Nil_construct (List T))
	end.

Hint Unfold split_comp_proj.

Solve Obligations with (repeat t462).
Fail Next Obligation.

Ltac rwrtTac_A199 := match goal with 
	| [ H1511: context[split ?T ?thiss58 ?seps] |- _ ] => 
			poseNew (Mark (T,thiss58,seps) "unfolding split_equation")
	| [  |- context[split ?T ?thiss58 ?seps] ] => 
			poseNew (Mark (T,thiss58,seps) "unfolding split_equation")
end.

Ltac rwrtTac_B199 := match goal with 
	| [ H1511: context[split ?T ?thiss58 ?seps], H2511: Marked (?T,?thiss58,?seps) "unfolding split_equation" |- _ ] => 
			let U199 := (fresh "U") in (poseNew (Mark (T,thiss58,seps) "unfolded split_equation");
			pose proof (split_equation_1 T thiss58 seps) as U199;
			rewrite U199 in *)
	| [ H2511: Marked (?T,?thiss58,?seps) "unfolding split_equation" |- context[split ?T ?thiss58 ?seps] ] => 
			let U199 := (fresh "U") in (poseNew (Mark (T,thiss58,seps) "unfolded split_equation");
			pose proof (split_equation_1 T thiss58 seps) as U199;
			rewrite U199 in *)
end.

Ltac rwrtTac199 := rwrtTac198; repeat rwrtTac_A199; repeat rwrtTac_B199.

Ltac t463 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac199 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t463.

(***********************
  End of split
 ***********************)

(***********************
  Start of splitAt
 ***********************)

Definition splitAt (T: Type) (thiss59: List T) (e3: T) : List (List T) :=
split T thiss59 (Cons_construct T e3 (Nil_construct T)).

Fail Next Obligation.

Hint Unfold splitAt: definitions.

(***********************
  End of splitAt
 ***********************)

(***********************
  Start of tailOption
 ***********************)

Definition tailOption (T: Type) (thiss60: List T) : {x___6: Option (List T) | (negb (Bool.eqb (isDefined (List T) x___6) (isEmpty T thiss60)) = true)} :=
match thiss60 with
| Cons_construct _ h25 t342 => Some_construct (List T) t342
| Nil_construct _ => None_construct (List T)
end.

Fail Next Obligation.

Hint Unfold tailOption: definitions.

(***********************
  End of tailOption
 ***********************)

(***********************
  Start of tails
 ***********************)


Definition tails_rt1_type (T: Type) (l5: List T) : Type :=
List (List T).

Fail Next Obligation.

Hint Unfold tails_rt1_type.


Equations tails (T: Type) (l5: List T) : tails_rt1_type T l5 := 
	tails T l5 by rec ignore_termination lt :=
	tails T l5 := match l5 with
	| Cons_construct _ _ tl => Cons_construct (List T) tl (tails T tl)
	| Nil_construct _ => 
			Cons_construct (List T) (Nil_construct T) (Nil_construct (List T))
	end.

Hint Unfold tails_comp_proj.

Solve Obligations with (repeat t463).
Fail Next Obligation.

Ltac rwrtTac_A200 := match goal with 
	| [ H1512: context[tails ?T ?l5] |- _ ] => 
			poseNew (Mark (T,l5) "unfolding tails_equation")
	| [  |- context[tails ?T ?l5] ] => poseNew (Mark (T,l5) "unfolding tails_equation")
end.

Ltac rwrtTac_B200 := match goal with 
	| [ H1512: context[tails ?T ?l5], H2512: Marked (?T,?l5) "unfolding tails_equation" |- _ ] => 
			let U200 := (fresh "U") in (poseNew (Mark (T,l5) "unfolded tails_equation");
			pose proof (tails_equation_1 T l5) as U200;
			rewrite U200 in *)
	| [ H2512: Marked (?T,?l5) "unfolding tails_equation" |- context[tails ?T ?l5] ] => 
			let U200 := (fresh "U") in (poseNew (Mark (T,l5) "unfolded tails_equation");
			pose proof (tails_equation_1 T l5) as U200;
			rewrite U200 in *)
end.

Ltac rwrtTac200 := rwrtTac199; repeat rwrtTac_A200; repeat rwrtTac_B200.

Ltac t464 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac200 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t464.

(***********************
  End of tails
 ***********************)

(***********************
  Start of take
 ***********************)


Definition take_rt5_type (T: Type) (thiss61: List T) (i1: Z) : Type :=
{res21: List T | (ifthenelse (set_subset (content T res21) (content T thiss61)) bool
	(fun _ => Zeq_bool (proj1_sig (size T res21)) (ifthenelse (Z.leb i1 (0)%Z) Z
		(fun _ => (0)%Z )
		(fun _ => ifthenelse (Z.geb i1 (proj1_sig (size T thiss61))) Z
			(fun _ => proj1_sig (size T thiss61) )
			(fun _ => i1 ) )) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold take_rt5_type.


Equations take (T: Type) (thiss61: List T) (i1: Z) : take_rt5_type T thiss61 i1 := 
	take T thiss61 i1 by rec ignore_termination lt :=
	take T thiss61 i1 := ifthenelse (isNil _ thiss61) (List T)
		(fun _ => Nil_construct T )
		(fun _ => ifthenelse (isCons _ thiss61) (List T)
			(fun _ => ifthenelse (Z.leb i1 (0)%Z) (List T)
				(fun _ => Nil_construct T )
				(fun _ => Cons_construct T (h T thiss61) (proj1_sig (take T (t4 T thiss61) (Z.sub i1 (1)%Z))) ) )
			(fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold take_comp_proj.

Solve Obligations with (repeat t464).
Fail Next Obligation.

Ltac rwrtTac_A201 := match goal with 
	| [ H1513: context[take ?T ?thiss61 ?i1] |- _ ] => 
			poseNew (Mark (T,thiss61,i1) "unfolding take_equation")
	| [  |- context[take ?T ?thiss61 ?i1] ] => 
			poseNew (Mark (T,thiss61,i1) "unfolding take_equation")
end.

Ltac rwrtTac_B201 := match goal with 
	| [ H1513: context[take ?T ?thiss61 ?i1], H2513: Marked (?T,?thiss61,?i1) "unfolding take_equation" |- _ ] => 
			let U201 := (fresh "U") in (poseNew (Mark (T,thiss61,i1) "unfolded take_equation");
			pose proof (take_equation_1 T thiss61 i1) as U201;
			rewrite U201 in *)
	| [ H2513: Marked (?T,?thiss61,?i1) "unfolding take_equation" |- context[take ?T ?thiss61 ?i1] ] => 
			let U201 := (fresh "U") in (poseNew (Mark (T,thiss61,i1) "unfolded take_equation");
			pose proof (take_equation_1 T thiss61 i1) as U201;
			rewrite U201 in *)
end.

Ltac rwrtTac201 := rwrtTac200; repeat rwrtTac_A201; repeat rwrtTac_B201.

Ltac t465 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac201 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t465.

(***********************
  End of take
 ***********************)

(***********************
  Start of evenSplit
 ***********************)

Definition evenSplit (T: Type) (thiss62: List T) : ((List T) * (List T))%type :=
let c := (Z.div (proj1_sig (size T thiss62)) (2)%Z) in ((proj1_sig (take T thiss62 c),proj1_sig (drop T thiss62 c))).

Fail Next Obligation.

Hint Unfold evenSplit: definitions.

(***********************
  End of evenSplit
 ***********************)

(***********************
  Start of rotate
 ***********************)

Definition rotate (T: Type) (thiss63: List T) (s3: Z) : {res22: List T | (Zeq_bool (proj1_sig (size T res22)) (proj1_sig (size T thiss63)) = true)} :=
ifthenelse (isEmpty T thiss63) (List T)
	(fun _ => Nil_construct T )
	(fun _ => proj1_sig (plus_plus_ T (proj1_sig (drop T thiss63 (Z.modulo s3 (proj1_sig (size T thiss63))))) (proj1_sig (take T thiss63 (Z.modulo s3 (proj1_sig (size T thiss63)))))) ).

Fail Next Obligation.

Hint Unfold rotate: definitions.

(***********************
  End of rotate
 ***********************)

(***********************
  Start of slice
 ***********************)

Definition slice (T: Type) (thiss64: List T) (from1: Z) (to1: Z) (contractHyp311: (ifthenelse
	(ifthenelse (Z.leb (0)%Z from1) bool
		(fun _ => Z.leb from1 to1 )
		(fun _ => false ))
	bool
	(fun _ => Z.leb to1 (proj1_sig (size T thiss64)) )
	(fun _ => false ) = true)) : List T :=
proj1_sig (take T (proj1_sig (drop T thiss64 from1)) (Z.sub to1 from1)).

Fail Next Obligation.

Hint Unfold slice: definitions.

(***********************
  End of slice
 ***********************)

(***********************
  Start of splitAtIndex
 ***********************)


Definition splitAtIndex_rt1_type (T: Type) (thiss65: List T) (index1: Z) : Type :=
{res23: ((List T) * (List T))%type | (ifthenelse
	(ifthenelse (propInBool ((proj1_sig (plus_plus_ T (fst res23) (snd res23)) = thiss65))) bool
		(fun _ => propInBool ((fst res23 = proj1_sig (take T thiss65 index1))) )
		(fun _ => false ))
	bool
	(fun _ => propInBool ((snd res23 = proj1_sig (drop T thiss65 index1))) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold splitAtIndex_rt1_type.


Equations splitAtIndex (T: Type) (thiss65: List T) (index1: Z) : splitAtIndex_rt1_type T thiss65 index1 := 
	splitAtIndex T thiss65 index1 by rec ignore_termination lt :=
	splitAtIndex T thiss65 index1 := match thiss65 with
	| Nil_construct _ => (Nil_construct T,Nil_construct T)
	| Cons_construct _ h26 rest1 => 
			ifthenelse (Z.leb index1 (0)%Z) (((List T) * (List T))%type)
				(fun _ => (Nil_construct T,thiss65) )
				(fun _ => let x___7 := ((fst (proj1_sig (splitAtIndex T rest1 (Z.sub index1 (1)%Z))),snd (proj1_sig (splitAtIndex T rest1 (Z.sub index1 (1)%Z))))) in (let right := (snd x___7) in ((Cons_construct T h26 (fst x___7),right))) )
	end.

Hint Unfold splitAtIndex_comp_proj.

Solve Obligations with (repeat t465).
Fail Next Obligation.

Ltac rwrtTac_A202 := match goal with 
	| [ H1514: context[splitAtIndex ?T ?thiss65 ?index1] |- _ ] => 
			poseNew (Mark (T,thiss65,index1) "unfolding splitAtIndex_equation")
	| [  |- context[splitAtIndex ?T ?thiss65 ?index1] ] => 
			poseNew (Mark (T,thiss65,index1) "unfolding splitAtIndex_equation")
end.

Ltac rwrtTac_B202 := match goal with 
	| [ H1514: context[splitAtIndex ?T ?thiss65 ?index1], H2514: Marked (?T,?thiss65,?index1) "unfolding splitAtIndex_equation" |- _ ] => 
			let U202 := (fresh "U") in (poseNew (Mark (T,thiss65,index1) "unfolded splitAtIndex_equation");
			pose proof (splitAtIndex_equation_1 T thiss65 index1) as U202;
			rewrite U202 in *)
	| [ H2514: Marked (?T,?thiss65,?index1) "unfolding splitAtIndex_equation" |- context[splitAtIndex ?T ?thiss65 ?index1] ] => 
			let U202 := (fresh "U") in (poseNew (Mark (T,thiss65,index1) "unfolded splitAtIndex_equation");
			pose proof (splitAtIndex_equation_1 T thiss65 index1) as U202;
			rewrite U202 in *)
end.

Ltac rwrtTac202 := rwrtTac201; repeat rwrtTac_A202; repeat rwrtTac_B202.

Ltac t466 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac202 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t466.

(***********************
  End of splitAtIndex
 ***********************)

(***********************
  Start of takeWhile
 ***********************)


Definition takeWhile_rt1_type (T: Type) (thiss66: List T) (p12: T -> bool) : Type :=
{res24: List T | (ifthenelse
	(ifthenelse (forall1 T res24 p12) bool
		(fun _ => Z.leb (proj1_sig (size T res24)) (proj1_sig (size T thiss66)) )
		(fun _ => false ))
	bool
	(fun _ => set_subset (content T res24) (content T thiss66) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold takeWhile_rt1_type.


Equations takeWhile (T: Type) (thiss66: List T) (p12: T -> bool) : takeWhile_rt1_type T thiss66 p12 := 
	takeWhile T thiss66 p12 by rec ignore_termination lt :=
	takeWhile T thiss66 p12 := ifthenelse
		(ifthenelse (isCons _ thiss66) bool
			(fun _ => p12 (h T thiss66) )
			(fun _ => false ))
		(List T)
		(fun _ => Cons_construct T (h T thiss66) (proj1_sig (takeWhile T (t4 T thiss66) p12)) )
		(fun _ => Nil_construct T ).

Hint Unfold takeWhile_comp_proj.

Solve Obligations with (repeat t466).
Fail Next Obligation.

Ltac rwrtTac_A203 := match goal with 
	| [ H1515: context[takeWhile ?T ?thiss66 ?p12] |- _ ] => 
			poseNew (Mark (T,thiss66,p12) "unfolding takeWhile_equation")
	| [  |- context[takeWhile ?T ?thiss66 ?p12] ] => 
			poseNew (Mark (T,thiss66,p12) "unfolding takeWhile_equation")
end.

Ltac rwrtTac_B203 := match goal with 
	| [ H1515: context[takeWhile ?T ?thiss66 ?p12], H2515: Marked (?T,?thiss66,?p12) "unfolding takeWhile_equation" |- _ ] => 
			let U203 := (fresh "U") in (poseNew (Mark (T,thiss66,p12) "unfolded takeWhile_equation");
			pose proof (takeWhile_equation_1 T thiss66 p12) as U203;
			rewrite U203 in *)
	| [ H2515: Marked (?T,?thiss66,?p12) "unfolding takeWhile_equation" |- context[takeWhile ?T ?thiss66 ?p12] ] => 
			let U203 := (fresh "U") in (poseNew (Mark (T,thiss66,p12) "unfolded takeWhile_equation");
			pose proof (takeWhile_equation_1 T thiss66 p12) as U203;
			rewrite U203 in *)
end.

Ltac rwrtTac203 := rwrtTac202; repeat rwrtTac_A203; repeat rwrtTac_B203.

Ltac t467 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac203 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t467.

(***********************
  End of takeWhile
 ***********************)

(***********************
  Start of toSet
 ***********************)

Definition toSet (T: Type) (thiss67: List T) : set (T) :=
foldLeft T (set (T)) thiss67 (@set_empty T) (fun x0___1 => fun x1___1 => set_union x0___1 (set_union (@set_empty T) (set_singleton x1___1))  ).

Fail Next Obligation.

Hint Unfold toSet: definitions.

(***********************
  End of toSet
 ***********************)

(***********************
  Start of toSet
 ***********************)

Definition toSet1 (T: Type) (thiss68: Option T) : set (T) :=
match thiss68 with
| None_construct _ => @set_empty T
| Some_construct _ x5 => set_union (@set_empty T) (set_singleton x5)
end.

Fail Next Obligation.

Hint Unfold toSet1: definitions.

(***********************
  End of toSet
 ***********************)

(***********************
  Start of unique
 ***********************)


Definition unique_rt1_type (T: Type) (thiss69: List T) : Type :=
List T.

Fail Next Obligation.

Hint Unfold unique_rt1_type.


Equations unique (T: Type) (thiss69: List T) : unique_rt1_type T thiss69 := 
	unique T thiss69 by rec ignore_termination lt :=
	unique T thiss69 := match thiss69 with
	| Nil_construct _ => Nil_construct T
	| Cons_construct _ h27 t404 => 
			Cons_construct T h27 (proj1_sig (minus_ T (unique T t404) h27))
	end.

Hint Unfold unique_comp_proj.

Solve Obligations with (repeat t467).
Fail Next Obligation.

Ltac rwrtTac_A204 := match goal with 
	| [ H1516: context[unique ?T ?thiss69] |- _ ] => 
			poseNew (Mark (T,thiss69) "unfolding unique_equation")
	| [  |- context[unique ?T ?thiss69] ] => 
			poseNew (Mark (T,thiss69) "unfolding unique_equation")
end.

Ltac rwrtTac_B204 := match goal with 
	| [ H1516: context[unique ?T ?thiss69], H2516: Marked (?T,?thiss69) "unfolding unique_equation" |- _ ] => 
			let U204 := (fresh "U") in (poseNew (Mark (T,thiss69) "unfolded unique_equation");
			pose proof (unique_equation_1 T thiss69) as U204;
			rewrite U204 in *)
	| [ H2516: Marked (?T,?thiss69) "unfolding unique_equation" |- context[unique ?T ?thiss69] ] => 
			let U204 := (fresh "U") in (poseNew (Mark (T,thiss69) "unfolded unique_equation");
			pose proof (unique_equation_1 T thiss69) as U204;
			rewrite U204 in *)
end.

Ltac rwrtTac204 := rwrtTac203; repeat rwrtTac_A204; repeat rwrtTac_B204.

Ltac t468 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac204 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t468.

(***********************
  End of unique
 ***********************)

(***********************
  Start of updated
 ***********************)


Definition contractHyp317_type (T: Type) (thiss70: List T) (i2: Z) (y: T) : Type :=
(ifthenelse (Z.leb (0)%Z i2) bool
	(fun _ => Z.ltb i2 (proj1_sig (size T thiss70)) )
	(fun _ => false ) = true).

Fail Next Obligation.

Hint Unfold contractHyp317_type.


Definition updated_rt1_type (T: Type) (thiss70: List T) (i2: Z) (y: T) (contractHyp317: contractHyp317_type T thiss70 i2 y) : Type :=
List T.

Fail Next Obligation.

Hint Unfold updated_rt1_type.


Equations updated (T: Type) (thiss70: List T) (i2: Z) (y: T) (contractHyp317: contractHyp317_type T thiss70 i2 y) : updated_rt1_type T thiss70 i2 y contractHyp317 := 
	updated T thiss70 i2 y contractHyp317 by rec ignore_termination lt :=
	updated T thiss70 i2 y contractHyp317 := ifthenelse
		(ifthenelse (isCons _ thiss70) bool
			(fun _ => Zeq_bool i2 (0)%Z )
			(fun _ => false ))
		(List T)
		(fun _ => Cons_construct T y (t4 T thiss70) )
		(fun _ => ifthenelse (isCons _ thiss70) (List T)
			(fun _ => Cons_construct T (h T thiss70) (updated T (t4 T thiss70) (Z.sub i2 (1)%Z) y _) )
			(fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold updated_comp_proj.

Solve Obligations with (repeat t468).
Fail Next Obligation.

Ltac rwrtTac_A205 := match goal with 
	| [ H1517: context[updated ?T ?thiss70 ?i2 ?y] |- _ ] => 
			poseNew (Mark (T,thiss70,i2,y) "unfolding updated_equation")
	| [  |- context[updated ?T ?thiss70 ?i2 ?y] ] => 
			poseNew (Mark (T,thiss70,i2,y) "unfolding updated_equation")
end.

Ltac rwrtTac_B205 := match goal with 
	| [ H1517: context[updated ?T ?thiss70 ?i2 ?y], H2517: Marked (?T,?thiss70,?i2,?y) "unfolding updated_equation" |- _ ] => 
			let U205 := (fresh "U") in (poseNew (Mark (T,thiss70,i2,y) "unfolded updated_equation");
			pose proof (updated_equation_1 T thiss70 i2 y) as U205;
			rewrite U205 in *)
	| [ H2517: Marked (?T,?thiss70,?i2,?y) "unfolding updated_equation" |- context[updated ?T ?thiss70 ?i2 ?y] ] => 
			let U205 := (fresh "U") in (poseNew (Mark (T,thiss70,i2,y) "unfolded updated_equation");
			pose proof (updated_equation_1 T thiss70 i2 y) as U205;
			rewrite U205 in *)
end.

Ltac rwrtTac205 := rwrtTac204; repeat rwrtTac_A205; repeat rwrtTac_B205.

Ltac t469 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac205 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t469.

(***********************
  End of updated
 ***********************)

(***********************
  Start of withFilter
 ***********************)

Definition withFilter (T: Type) (thiss71: List T) (p13: T -> bool) : List T :=
proj1_sig (filter1 T thiss71 p13).

Fail Next Obligation.

Hint Unfold withFilter: definitions.

(***********************
  End of withFilter
 ***********************)

(***********************
  Start of withFilter
 ***********************)

Definition withFilter1 (T: Type) (thiss72: Option T) (p14: T -> bool) : Option T :=
filter T thiss72 p14.

Fail Next Obligation.

Hint Unfold withFilter1: definitions.

(***********************
  End of withFilter
 ***********************)

(***********************
  Start of zip
 ***********************)


Definition zip_rt1_type (T: Type) (B: Type) (thiss73: List T) (that3: List B) : Type :=
{x___31: List ((T * B)%type) | (Zeq_bool (proj1_sig (size ((T * B)%type) x___31)) (ifthenelse (Z.leb (proj1_sig (size T thiss73)) (proj1_sig (size B that3))) Z
	(fun _ => proj1_sig (size T thiss73) )
	(fun _ => proj1_sig (size B that3) )) = true)}.

Fail Next Obligation.

Hint Unfold zip_rt1_type.


Equations zip (T: Type) (B: Type) (thiss73: List T) (that3: List B) : zip_rt1_type T B thiss73 that3 := 
	zip T B thiss73 that3 by rec ignore_termination lt :=
	zip T B thiss73 that3 := ifthenelse
		(ifthenelse (isCons _ thiss73) bool
			(fun _ => isCons _ that3 )
			(fun _ => false ))
		(List ((T * B)%type))
		(fun _ => Cons_construct ((T * B)%type) ((h T thiss73,h B that3)) (proj1_sig (zip T B (t4 T thiss73) (t4 B that3))) )
		(fun _ => Nil_construct ((T * B)%type) ).

Hint Unfold zip_comp_proj.

Solve Obligations with (repeat t469).
Fail Next Obligation.

Ltac rwrtTac_A206 := match goal with 
	| [ H1518: context[zip ?T ?B ?thiss73 ?that3] |- _ ] => 
			poseNew (Mark (T,B,thiss73,that3) "unfolding zip_equation")
	| [  |- context[zip ?T ?B ?thiss73 ?that3] ] => 
			poseNew (Mark (T,B,thiss73,that3) "unfolding zip_equation")
end.

Ltac rwrtTac_B206 := match goal with 
	| [ H1518: context[zip ?T ?B ?thiss73 ?that3], H2518: Marked (?T,?B,?thiss73,?that3) "unfolding zip_equation" |- _ ] => 
			let U206 := (fresh "U") in (poseNew (Mark (T,B,thiss73,that3) "unfolded zip_equation");
			pose proof (zip_equation_1 T B thiss73 that3) as U206;
			rewrite U206 in *)
	| [ H2518: Marked (?T,?B,?thiss73,?that3) "unfolding zip_equation" |- context[zip ?T ?B ?thiss73 ?that3] ] => 
			let U206 := (fresh "U") in (poseNew (Mark (T,B,thiss73,that3) "unfolded zip_equation");
			pose proof (zip_equation_1 T B thiss73 that3) as U206;
			rewrite U206 in *)
end.

Ltac rwrtTac206 := rwrtTac205; repeat rwrtTac_A206; repeat rwrtTac_B206.

Ltac t470 :=
  t_base ||
  List_tactic77 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  autounfold with definitions in * ||
  rwrtTac206 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t470.

(***********************
  End of zip
 ***********************)

