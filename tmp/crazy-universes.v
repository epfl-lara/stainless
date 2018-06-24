Require Import SLC.Lib.
Require Import SLC.PropBool.
Require Import SLC.Booleans.
Require Import stdpp.set.
Require Import SLC.stdppSets.
Require Import SLC.Tactics.
Require Import SLC.Ints.
Set Program Mode.
Ltac t183 :=
  t_base ||
  idtac ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in * ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t183.


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

Lemma None_exists: (forall T: Type, forall self312: Option T, ((true = isNone T self312)) <-> (((None_construct T = self312)))). 
Proof.
	repeat t183 || eauto.
Qed.

Lemma Some_exists: (forall T: Type, forall self313: Option T, ((true = isSome T self313)) <-> ((exists tmp117: T, (Some_construct T tmp117 = self313)))). 
Proof.
	repeat t183 || eauto.
Qed.

Definition None_type (T: Type) : Type :=
{src: Option T | (isNone T src = true)}.

Fail Next Obligation.

Hint Unfold  None_type: refinements. 

Definition Some_type (T: Type) : Type :=
{src: Option T | (isSome T src = true)}.

Fail Next Obligation.

Hint Unfold  Some_type: refinements. 

Ltac Option_tactic39 := match goal with 
	| [ H156: (true = isNone ?T ?self314) |- _ ] => 
			poseNew (Mark (T,self314) "None_exists");
			pose proof ((proj1 (None_exists _ _)) H156)
	| [ H156: (isNone ?T ?self314 = true) |- _ ] => 
			poseNew (Mark (T,self314) "None_exists");
			pose proof ((proj1 (None_exists _ _)) (eq_sym H156))
	| [ H157: (true = isSome ?T ?self315) |- _ ] => 
			poseNew (Mark (T,self315) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) H157)
	| [ H157: (isSome ?T ?self315 = true) |- _ ] => 
			poseNew (Mark (T,self315) "Some_exists");
			pose proof ((proj1 (Some_exists _ _)) (eq_sym H157))
	| _ => idtac
end.

Ltac t184 :=
  t_base ||
  Option_tactic39 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in * ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t184.


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

Lemma Cons_exists: (forall T: Type, forall self316: List T, ((true = isCons T self316)) <-> ((exists tmp119: List T, exists tmp118: T, (Cons_construct T tmp118 tmp119 = self316)))). 
Proof.
	repeat t184 || eauto.
Qed.

Lemma Nil_exists: (forall T: Type, forall self317: List T, ((true = isNil T self317)) <-> (((Nil_construct T = self317)))). 
Proof.
	repeat t184 || eauto.
Qed.

Definition Cons_type (T: Type) : Type :=
{src: List T | (isCons T src = true)}.

Fail Next Obligation.

Hint Unfold  Cons_type: refinements. 

Definition Nil_type (T: Type) : Type :=
{src: List T | (isNil T src = true)}.

Fail Next Obligation.

Hint Unfold  Nil_type: refinements. 

Ltac List_tactic39 := match goal with 
	| [ H158: (true = isCons ?T ?self318) |- _ ] => 
			poseNew (Mark (T,self318) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) H158)
	| [ H158: (isCons ?T ?self318 = true) |- _ ] => 
			poseNew (Mark (T,self318) "Cons_exists");
			pose proof ((proj1 (Cons_exists _ _)) (eq_sym H158))
	| [ H159: (true = isNil ?T ?self319) |- _ ] => 
			poseNew (Mark (T,self319) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) H159)
	| [ H159: (isNil ?T ?self319 = true) |- _ ] => 
			poseNew (Mark (T,self319) "Nil_exists");
			pose proof ((proj1 (Nil_exists _ _)) (eq_sym H159))
	| _ => Option_tactic39
end.

Ltac t185 :=
  t_base ||
  List_tactic39 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in * ||
  idtac ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t185.

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
  Start of content
 ***********************)

Obligation Tactic:=idtac.
Definition content_rt12_type (T: Type) (thiss1: List T) : Type :=
set (T).

Fail Next Obligation.

Hint Unfold content_rt12_type.


Equations (noind) content (T: Type) (thiss1: List T) : content_rt12_type T thiss1 := 
	content T thiss1 by rec ignore_termination lt :=
	content T thiss1 := match thiss1 with
	| Nil_construct _ => @set_empty T
	| Cons_construct _ h1 t9 => 
			set_union (set_union (@set_empty T) (set_singleton h1)) (content T t9)
	end.

Hint Unfold content_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A46 := match goal with 
	| [ H1206: context[content ?T ?thiss1] |- _ ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
	| [  |- context[content ?T ?thiss1] ] => 
			poseNew (Mark (T,thiss1) "unfolding content_equation")
end.

Ltac rwrtTac_B46 := match goal with 
	| [ H1206: context[content ?T ?thiss1], H2206: Marked (?T,?thiss1) "unfolding content_equation" |- _ ] => 
			let U46 := (fresh "U") in (poseNew (Mark (T,thiss1) "unfolded content_equation");
			pose proof (content_equation_1 T thiss1) as U46;
			pose proof (Mark (U46) "equation"))
	| [ H2206: Marked (?T,?thiss1) "unfolding content_equation" |- context[content ?T ?thiss1] ] => 
			let U46 := (fresh "U") in (poseNew (Mark (T,thiss1) "unfolded content_equation");
			pose proof (content_equation_1 T thiss1) as U46;
			pose proof (Mark (U46) "equation"))
end.

Ltac rwrtTac46 := idtac; repeat rwrtTac_A46; repeat rwrtTac_B46.

Ltac t186 :=
  t_base ||
  List_tactic39 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in * ||
  rwrtTac46 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t186.

(***********************
  End of content
 ***********************)

(***********************
  Start of size
 ***********************)

Obligation Tactic:=idtac.
Definition size_rt8_type (T: Type) (thiss30: List T) : Type :=
{x___11: Z | (Z.geb x___11 (0)%Z = true)}.

Fail Next Obligation.

Hint Unfold size_rt8_type.


Equations (noind) size (T: Type) (thiss30: List T) : size_rt8_type T thiss30 := 
	size T thiss30 by rec ignore_termination lt :=
	size T thiss30 := match thiss30 with
	| Nil_construct _ => (0)%Z
	| Cons_construct _ h12 t130 => Z.add (1)%Z (proj1_sig (size T t130))
	end.

Hint Unfold size_comp_proj.

Admit Obligations.
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A47 := match goal with 
	| [ H1207: context[size ?T ?thiss30] |- _ ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
	| [  |- context[size ?T ?thiss30] ] => 
			poseNew (Mark (T,thiss30) "unfolding size_equation")
end.

Ltac rwrtTac_B47 := match goal with 
	| [ H1207: context[size ?T ?thiss30], H2207: Marked (?T,?thiss30) "unfolding size_equation" |- _ ] => 
			let U47 := (fresh "U") in (poseNew (Mark (T,thiss30) "unfolded size_equation");
			pose proof (size_equation_1 T thiss30) as U47;
			pose proof (Mark (U47) "equation"))
	| [ H2207: Marked (?T,?thiss30) "unfolding size_equation" |- context[size ?T ?thiss30] ] => 
			let U47 := (fresh "U") in (poseNew (Mark (T,thiss30) "unfolded size_equation");
			pose proof (size_equation_1 T thiss30) as U47;
			pose proof (Mark (U47) "equation"))
end.

Ltac rwrtTac47 := rwrtTac46; repeat rwrtTac_A47; repeat rwrtTac_B47.

Ltac t187 :=
  t_base ||
  List_tactic39 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in * ||
  rwrtTac47 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t187.

(***********************
  End of size
 ***********************)


(***********************
  Start of drop
 ***********************)


Definition drop_rt_type (T: Type) (thiss38: List T) (i: Z) : Type :=
{res8: List T | (ifthenelse (set_subset (content T res8) (content T thiss38)) bool
	(fun _ => Zeq_bool (proj1_sig (size T res8)) (ifthenelse (Z.leb i (0)%Z) Z
		(fun _ => proj1_sig (size T thiss38) )
		(fun _ => ifthenelse (Z.geb i (proj1_sig (size T thiss38))) Z
			(fun _ => (0)%Z )
			(fun _ => Z.sub (proj1_sig (size T thiss38)) i ) )) )
	(fun _ => false ) = true)}.

Fail Next Obligation.

Hint Unfold drop_rt_type.


Equations (noind) drop (T: Type) (thiss38: List T) (i: Z) : drop_rt_type T thiss38 i := 
	drop T thiss38 i by rec ignore_termination lt :=
	drop T thiss38 i := ifthenelse (isNil _ thiss38) (List T)
		(fun _ => Nil_construct T )
		(fun _ => ifthenelse (isCons _ thiss38) (List T)
			(fun _ => ifthenelse (Z.leb i (0)%Z) (List T)
				(fun _ => Cons_construct T (h T thiss38) (t4 T thiss38) )
				(fun _ => proj1_sig (drop T (t4 T thiss38) (Z.sub i (1)%Z)) ) )
			(fun _ => let contradiction: False := _ in match contradiction with end ) ).

Hint Unfold drop_comp_proj.

Obligation Tactic := idtac.

Next Obligation. repeat t187. Qed.
Next Obligation. repeat t187. Qed.
  t187. t187. t187. t187. t187.
  t187. t187. t187. t187. t187.
  t187. t187. t187. t187. t187.
  t187. t187. t187. t187. t187.
  t187. t187. t187. t187. t187.
  t187. t187. t187. t187. t187.
  t187. t187. t187. t187. t187.
  t187. t187. t187. t187. t187.
  t187. t187. t187. t187. t187.
  t187. t187. t187. t187. t187.
  - repeat t187.
  - repeat t187.
  - repeat t187.
  - repeat t187.
  - t187. t187. t187. t187. t187.
    t187. t187. t187. t187. t187.
    t187. t187. t187. t187. t187.
    t187. t187. t187. t187. t187.
    t187. t187. t187. t187. t187.
    t187. t187. t187. t187. t187.
    t187. t187. t187. t187. t187.
    + repeat t187.
    + repeat t187.
    + t187. t187. t187. t187. t187.
      t187. t187. t187. t187. t187.
      t187. t187. t187. t187. t187.
      t187. t187. t187. t187. t187.
      t187. t187. t187. t187. t187.
      t187. t187. t187. t187. t187.
      * t187. t187. t187. t187. t187.
         t187. t187. t187. t187. t187.
          t187. t187. t187. t187. t187.
           t187. t187. t187. t187. t187.
            t187. t187. t187. t187. t187.
             t187. t187. t187. t187. t187.
             -- repeat t187.
             -- repeat t187.
      * repeat t187.
   + t187. t187. t187. t187. t187.
      t187. t187. t187. t187. t187.
       t187. t187. t187. t187. t187.
        t187. t187. t187. t187. t187.
         t187. t187. t187. t187. t187.
          t187. t187. t187. t187. t187.
           t187. t187. t187. t187. t187.
      * repeat t187.
      * repeat t187.
      *  t187. t187. t187. t187. t187.
         t187. t187. t187. t187. t187.
         t187. t187. t187. t187. t187.
         t187. t187. t187. t187. t187.
         t187. t187. t187. t187. t187.
         t187. t187. t187. t187. t187.
         --  t187. t187. t187. t187. t187.
             t187. t187. t187. t187. t187.
             t187. t187. t187. t187. t187.
             t187. t187. t187. t187. t187.
             t187. t187. t187. t187. t187.
             t187. t187. t187. t187. t187.
             t187. t187. t187. t187. t187.
             ++ repeat t187.
             ++ repeat t187.
             ++ t187. t187. t187. t187. t187.
                t187. t187. t187. t187. t187.
                t187. t187. t187. t187. t187.
                t187. t187. t187. t187. t187.
                t187. t187. t187. t187. t187.
                t187. t187. t187. t187. t187.
                ** repeat t187.
                ** repeat t187.
                ** repeat t187.
        -- repeat t187.
Qed.
           

Solve Obligations with (repeat t187).
Obligation Tactic := idtac.

Fail Next Obligation.

Ltac rwrtTac_A48 := match goal with 
	| [ H1208: context[drop ?T ?thiss38 ?i] |- _ ] => 
			poseNew (Mark (T,thiss38,i) "unfolding drop_equation")
	| [  |- context[drop ?T ?thiss38 ?i] ] => 
			poseNew (Mark (T,thiss38,i) "unfolding drop_equation")
end.

Ltac rwrtTac_B48 := match goal with 
	| [ H1208: context[drop ?T ?thiss38 ?i], H2208: Marked (?T,?thiss38,?i) "unfolding drop_equation" |- _ ] => 
			let U48 := (fresh "U") in (poseNew (Mark (T,thiss38,i) "unfolded drop_equation");
			pose proof (drop_equation_1 T thiss38 i) as U48;
			pose proof (Mark (U48) "equation"))
	| [ H2208: Marked (?T,?thiss38,?i) "unfolding drop_equation" |- context[drop ?T ?thiss38 ?i] ] => 
			let U48 := (fresh "U") in (poseNew (Mark (T,thiss38,i) "unfolded drop_equation");
			pose proof (drop_equation_1 T thiss38 i) as U48;
			pose proof (Mark (U48) "equation"))
end.

Ltac rwrtTac48 := rwrtTac47; repeat rwrtTac_A48; repeat rwrtTac_B48.

Ltac t188 :=
  t_base ||
  List_tactic39 ||
  slow ||
  t_sets ||
  ifthenelse_step ||
  rewrite_ifthenelse ||
  destruct_ifthenelse ||
  (progress autorewrite with libCase in *) ||
  autounfold with definitions in * ||
  rwrtTac48 ||
  autounfold with recognizers in *.

Obligation Tactic := repeat t188.

(***********************
  End of drop
 ***********************)
