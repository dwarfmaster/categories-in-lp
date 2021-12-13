
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
Require Import Misc.
Require Import Limits.Graph.

Local Open Scope morphism_scope.

Section Product.
  Context {C : PreCategory}.

  Definition ProductGr (a b : object C) : Graph C (Fin 2) Empty.
  Proof.
    srapply mkGraph; intro x.
    - destruct x; [ exact b | exact a ].
    - empty_ind.
  Defined.
  Definition Product (a b : object C) := Limit (ProductGr a b).
  Definition AllProducts := forall(a b : object C), Product a b.
  Definition prod_obj {a b : object C} (p : Product a b) : object C :=
    cn_top (lim_cone p).
  Definition pi1 {a b : object C} (p : Product a b) : morphism C (prod_obj p) a :=
    cn_side (lim_cone p) fin1.
  Definition pi2 {a b : object C} (p : Product a b) : morphism C (prod_obj p) b :=
    cn_side (lim_cone p) fin2.

  Definition prod_cone {a b c : object C} (f : morphism C c a) (g : morphism C c b) :
    Cone (ProductGr a b).
  Proof.
    srapply mkCone.
    - exact c.
    - intro n; destruct n; [ exact g | exact f ].
    - empty_ind'.
  Defined.
  Lemma product_ex {a b : object C} (P : Product a b) :
    forall(c : object C), forall(f : morphism C c a), forall(g : morphism C c b),
      exists(e : morphism C c (prod_obj P)), f = pi1 P o e /\ g = pi2 P o e.
  Proof.
    intros c f g. pose (cn := prod_cone f g). pose (mph := lim_ex P cn). exists(cnmph_mph mph).
    split; [ pose (Hcomm := cnmph_comm mph fin1)
           | pose (Hcomm := cnmph_comm mph fin2) ];
      symmetry; exact Hcomm.
  Qed.

  Definition prod_mph {a b c : object C} (f : morphism C c a) (g : morphism C c b) :
    forall(cn : Cone (ProductGr a b)), forall(m : morphism C c (cn_top cn)),
      cn_side cn fin1 o m = f ->
      cn_side cn fin2 o m = g ->
      ConeMorphism (prod_cone f g) cn.
  Proof.
    intros cn m H1 H2. srapply mkCnMph; [ exact m | idtac ].
    intro n; destruct n; try (destruct u).
    - destruct f0; try (destruct u); [ empty_ind | idtac ].
      rewrite H2. reflexivity.
    - rewrite H1. reflexivity.
  Defined.
  Lemma product_uniq {a b : object C} (P : Product a b):
    forall(c : object C), forall(m1 m2 : morphism C c (prod_obj P)),
      pi1 P o m1 = pi1 P o m2 -> pi2 P o m1 = pi2 P o m2 -> m1 = m2.
  Proof.
    intros c m1 m2 Hpi1 Hpi2.
    pose (mph1 := prod_mph (pi1 P o m1) (pi2 P o m1) (lim_cone P) m1 1 1).
    pose (mph2 := prod_mph (pi1 P o m1) (pi2 P o m1) (lim_cone P) m2 Hpi1^ Hpi2^).
    exact (lim_uniq P _ mph1 mph2).
  Qed.

End Product.
