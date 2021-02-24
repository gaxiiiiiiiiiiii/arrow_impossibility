From mathcomp Require Export finset fintype eqtype.
Require Export ssrbool ssrfun Init ssreflect Bool Classical.

Notation "x ∈ X" := (in_mem x (mem X))(at level 10).
Notation "X ⊂ Y" := (X \subset Y)(at level 10).
Notation "X ∩ Y" := (setI X Y)(at level 60).
Notation "X ∪ Y" := (setU X Y) (at level 10).
Notation "¬ X" := (setC X)(at level 5).
Notation "X ~ Y"  := (setD X Y) (at level 10).


Parameter Choice: finType.
Definition Rel := {set prod_finType Choice Choice}.

Definition P (R : Rel) := 
  [set u  in R | ~~ (u.2, u.1) ∈ R].

Definition I (R : Rel) := 
  [set u in R | (u.2, u.1) ∈ R].




Definition reflective (R : Rel) :=
    forall x, (x,x) ∈ R.

Definition transitive (R : Rel) :=
    forall x y z, (x,y) ∈ R -> (y,z) ∈ R -> (x,z) ∈ R.

Definition complete (R : Rel) :=
    forall x y, x <> y -> (x,y) ∈ R || (y,x) ∈ R.


Inductive trans_closure (R : Rel) (x z : Choice) : Type :=
  | pure_trans y : (x,y) ∈  R  -> (y,z) ∈ R -> (x,z) ∈ R ->  trans_closure R x z
  | step_trans y : trans_closure R x y -> (y,z) ∈ R -> (x,z) ∈ R -> trans_closure R x z.

Definition acyclic R :=
    forall x y, trans_closure R x y -> ~~ (y,x) ∈ R.

Parameter reflectiveB : Rel -> bool.
Parameter transitiveB : Rel -> bool.
Parameter completeB : Rel -> bool.
Parameter acyclicB : Rel -> bool.      

Axiom reflectiveP : forall R, reflect (reflective R) (reflectiveB R).
Axiom transitiveP : forall R, reflect (transitive R) (transitiveB R).
Axiom completeP : forall R, reflect (complete R) (completeB R).
Axiom acyclicP : forall R, reflect (acyclic R) (acyclicB R).

Hint Resolve reflectiveP transitiveP completeP acyclicP : relation.

Definition order R :=
    reflective R /\ complete R /\ transitive R.

Parameter orderB : Rel -> bool.

Axiom orderP : forall R, reflect (order R) (orderB R).  

Definition quasi_orderB R :=
  reflectiveB R && completeB R && transitiveB (P R).

Definition acyclic_orderB R :=
  reflectiveB R && completeB R && acyclicB R.

Definition pre_orderB R :=
  reflectiveB R && transitiveB R.


Theorem PI_R (R : Rel):
  (P R)  ∪ (I R) = R.
Proof.
  apply setP => x.
  rewrite in_setU.
  rewrite !in_set.
  case (x ∈ R) => //=.
  apply orNb.
Qed.

Theorem transI R x y z :
  transitive R -> (x,y) ∈ (I R) -> (y,z) ∈ (I R) -> (x,z) ∈ (I R).
Proof.
  rewrite /I !in_set => /=.
  move => trans.
  move /andP => [xy yx].
  move /andP => [yz zy].
  move : (trans x y z xy yz) => zx.
  move : (trans z y x zy yx) => xz.
  by apply andb_true_intro.
Qed.  

Theorem IPP R x y z :
  transitive R -> (x,y) ∈ (P R) -> (y,z) ∈ (I R) -> (x,z) ∈ (P R).
Proof.
  rewrite /I !in_set => /=.
  move =>  trans.
  move /andP => [xy _yx].
  move /andP => [yz zy].
  apply andb_true_intro.
  split.
  + apply (trans x y z) => //.
  + rewrite negb_true_iff.
    move /negb_true_iff in _yx.
    move : (trans y z x yz).
    case /imply_to_or => H.
    - apply not_true_is_false => //.
    - rewrite H in _yx.
      case (_yx).
      apply (trans z y x) => //.
Qed.      


Theorem PIP R x y z :
  transitive R -> (x,y) ∈ (I R) -> (y,z) ∈ (P R) -> (x,z) ∈ (P R).
Proof.
  rewrite /I !in_set => /=.
  move =>  trans.
  move /andP => [xy yx].
  move /andP => [yz _zy].
  apply andb_true_intro.
  split.
  + apply (trans x y z) => //.
  + rewrite negb_true_iff.
    move /negb_true_iff in _zy.
    move : (trans z x y).
    case /imply_to_or => H.
    - apply not_true_is_false => //.
    - rewrite (H xy) in _zy.
      case (_zy).
      apply (trans z y x) => //.
Qed.


Theorem transP R x y z:
  transitive R -> (x,y) ∈ (P R) -> (y,z) ∈ (P R) -> (x,z) ∈ (P R).
Proof.
  rewrite /I !in_set => /=.
  move =>  trans.
  move /andP => [xy _yx].
  move /andP => [yz _zy].
  apply andb_true_intro.
  split.
  + apply (trans x y z) => //.
  + rewrite negb_true_iff.
    move /negb_true_iff in _zy.
    move /negb_true_iff in _yx.
    apply not_true_is_false => F.
    apply not_true_iff_false in _zy.
    apply _zy.
    apply (trans z x y) => //.
Qed.  

Theorem P_R R x :
    x ∈ (P R) -> x ∈ R.
Proof.
  rewrite in_set.
  move /andP => [H _] => //.
Qed.  