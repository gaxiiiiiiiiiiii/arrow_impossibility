


(* 


(* H : 投票者 *)
(* X : 選択肢 *)
Definition C_set := {set Choice}.
Parameter Choicer : finType.
Parameter X : {set Choice}.
Parameter H : {set Choicer}. 
Parameter n : nat.
Axiom n_gt_1 : n > 1.
Axiom H_card : #|H| = n.
Axiom X_card : 2 < #|X|.

Definition pow_X := powerset X ~ [set φ].
Definition pow_Rel := powerset (setX X X).
Definition all_order := [set R in pow_Rel| orderB R].
Definition restrict (R : Rel) S := [set u in R | u ∈ (setX S S)].
Notation "R | ( S )" := (restrict R S)(at level 10).

(* 各個人の選好を導く関数 *)
Definition indiv_choice_func := Choicer -> Rel.
(* プロファイル付き集合値選択関数：プロファイルから社会全体の選好を導く関数 *)
Definition setvalue_choice_func := {set set_of_finType (prod_finType Choice Choice)} -> Rel.
(* 集合値選択関数：選択肢の集合を絞る関数 *)  
Definition set_choice_func := C_set -> C_set.
(* 各個人の選好の集合 *)  
Definition profile (f : indiv_choice_func) := f @: H.


(* 集合値選択関数の整合性の条件 *)  
Definition α := 
  forall S1 S2 : C_set, S1 ⊂ S2 -> 
  (forall x (C : set_choice_func), 
   x ∈ S1 -> x ∈ (C S2) -> x ∈ (C S1)).

Definition β' := 
  forall S1 S2 : C_set, S1 ⊂ S2 -> 
  (forall x y (C : set_choice_func), 
    x ∈ S1 -> y ∈ S1 -> x ∈ (C S1) -> y ∈ (C S2) -> x ∈ (C S2)).

Definition β :=
  forall S1 S2 : C_set, S1 ⊂ S2 ->
  (forall x y (C : set_choice_func), 
   x ∈ S1 -> y ∈ S2 -> x ∈ (C S1) -> y ∈ (C S1 ∩ C S2) -> x ∈ (C S2)).

Definition δ :=
  forall S1 S2 : C_set, S1 ⊂ S2 ->
  (forall (x y : Choice) (C : set_choice_func), 
  x ∈ S1 -> y ∈ S2 -> x <> y -> x ∈ (C S1) -> y ∈ (C S1) -> [set x] <> C S2).

Definition γ :=
   forall (C : set_choice_func) (S : C_set) x,
  (forall Si : C_set, Si ⊂ S /\ Si <> S /\ Si <> φ -> x ∈ (C Si)) -> x ∈ (C S).

Definition path_independence :=
  forall (C : set_choice_func) (S1 S2 : C_set),
  (C (S1 ∪ S2)) = C ((C S1) ∪ (C S2)).    

  (*  最良関数 *)

Definition greatest (x : Choice) (S : C_set) (R : Rel) :=
    forall y, y ∈ S -> (x,y) ∈ R.

Parameter greatestB : Choice -> C_set -> Rel -> bool.

Axiom greatestP : forall x S R, reflect (greatest x S R) (greatestB x S R).  


Definition greatesst_func (S : C_set) (R : Rel) :=
  [set x in S | greatestB x S R].


Lemma greatest_not_empty S R:
  greatesst_func S R != φ <-> acyclic_orderB R.
Proof.
Admitted.

(* 正規性 *)

Definition normality C :=
    exists R, forall S, C S = greatesst_func S R.
    

  

   *)



    
    










