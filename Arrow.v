Require Export Relation.

Parameter Choicer : finType.
Parameter X : {set Choice}.
Parameter H : {set Choicer}. 
Parameter n : nat.
Axiom n_gt_1 : n > 1.
Axiom H_card : #|H| = n.
Axiom X_card : 2 < #|X|.
Definition φ := set0 (T := Choice).

Definition O := 
  [set R : Rel | R ⊂ (setX X X) && orderB R].

Definition D := powerset O.  

(* 各個人の選好を導く関数  fi*)
Definition indiv_choice_func := 
  Choicer -> Rel.

Axiom Ri_D :
  forall (f : indiv_choice_func) (i : Choicer), (f i) ∈ O.



(* 各個人の選好の集合 : {Ri} *)  
Definition profile (f : indiv_choice_func) (H : {set Choicer}):= 
  f @: H.

(* プロファイル付き集合値選択関数：プロファイルから社会全体の選好を導く関数 *)
Definition SWF := 
  {set set_of_finType (prod_finType Choice Choice)} -> Rel.

  


(* 定義域 *)    
Definition U (f : SWF) :=
  forall fi, (profile fi H) ∈ D -> (f (profile fi H)) ∈ O.
    
(* 弱パレート原理 *)    
Definition WP (f : SWF) :=
  forall fi x y, (profile fi H) ∈ D -> x ∈ X -> y ∈ X ->
  (forall i, i ∈ H -> (x,y) ∈ (P (fi i))) -> (x,y) ∈ (P (f (profile fi H))).


(* 無関係な選択肢からの独立性 *)
Definition IIA (f : SWF)  :=
    forall fi gi x y, (profile fi H) ∈ D -> (profile gi H) ∈ D -> x ∈ X -> y ∈ X ->
    (forall i, i ∈ H -> ((x,y) ∈ (fi i) <-> (x,y) ∈ (gi i)) /\ ((y,x) ∈ (fi i) <-> (y,x) ∈ (gi i))) ->
    ((x,y) ∈ (f (profile fi H)) <-> (x,y) ∈ (f (profile gi H))) /\ ((y,x) ∈ (f (profile fi H)) <-> (y,x) ∈ (f (profile gi H))).

(* 非独裁性 *)      
Definition ND (f : SWF)  :=
      ~ exists i, i ∈ H /\ 
      (forall fi x y , (profile fi H) ∈ D -> x ∈ X -> y ∈ X -> 
       (x,y) ∈ (P (fi i)) -> (x,y) ∈ (P (f (profile fi H)))).

Definition Arrow :=
  ~ exists f : SWF, U f  /\ WP f  /\ IIA f  /\ ND f .

Definition isDictator (i : Choicer) (f : SWF) :=
  i ∈ H /\
  (forall fi x y , (profile fi H) ∈ D -> x ∈ X -> y ∈ X -> 
    (x,y) ∈ (P (fi i)) -> (x,y) ∈ (P (f (profile fi H)))).

(* Definition ADec (V : {set Choicer}) (f : SWF) :=
  V ⊂ H /\ V != set0 (T := Choicer) /\
  (exists x y, x ∈ X /\ y ∈ X /\
  (forall fi, (profile fi H) ∈ D -> 
  (forall i, i ∈ V -> (x,y) ∈ (P (fi i))) /\ (forall i, i ∈ (H ~ V) -> (y,x) ∈ (P (fi i))) ->
   (x,y) ∈ (P (f (profile fi H))))).

Definition ADec_ (V : {set Choicer}) (f : SWF) (X : {set Choice}) (x y : Choice):=
  V ⊂ H /\ V != set0 (T := Choicer) /\ x ∈ X /\ y ∈ X /\
  (forall fi, (profile fi H) ∈ D -> 
  (forall i, i ∈ V -> (x,y) ∈ (P (fi i))) /\ (forall i, i ∈ (H ~ V) -> (y,x) ∈ (P (fi i))) ->
  (x,y) ∈ (P (f (profile fi H)))).
  
Lemma ADAD  (V : {set Choicer}) (f : SWF) (X : {set Choice}) (x y : Choice) :
    ADec_ V f X x y -> ADec V f X.
Proof.
  move => [a [b [c [d H]]]].
  split => //.
  split => //.
  exists x, y => //.
Qed.  

Definition Dec (V : {set Choicer}) (f : SWF) (X : {set Choice}):=
  V ⊂ H /\ V != set0 (T := Choicer) /\
  (exists x y, x ∈ X /\ y ∈ X /\
  (forall fi i, (profile fi H) ∈ D -> i ∈ V ->
  (x,y) ∈ (P (fi i)) -> (x,y) ∈ (P (f (profile fi H))))).
 *)
