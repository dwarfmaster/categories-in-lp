
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
From HoTT Require Import Categories.InitialTerminalCategory.Functors.
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

  Lemma product_ex_comm {a b c d : object C} (Pab : Product a b) (Pcd : Product c d) :
    forall{e : object C}, forall(fa : morphism C e a), forall(fb : morphism C e b),
    forall(fc : morphism C a c), forall(fd : morphism C b d),
      proj1 (product_ex Pcd _ (fc o pi1 Pab) (fd o pi2 Pab)) o proj1 (product_ex Pab _ fa fb)
            = proj1 (product_ex Pcd _ (fc o fa) (fd o fb)).
  Proof.
    intros e fa fb fc fd.
    destruct (product_ex Pcd _ (fc o pi1 Pab) (fd o pi2 Pab)) as [ p1 [ H11 H12 ] ].
    destruct (product_ex Pab _ fa fb) as [ p2 [ H21 H22 ] ].
    destruct (product_ex Pcd _ (fc o fa) (fd o fb)) as [ p3 [ H31 H32 ] ].
    simpl; apply product_uniq.
    - rewrite <- associativity. rewrite <- H11.
      rewrite associativity. rewrite <- H21. assumption.
    - rewrite <- associativity. rewrite <- H12.
      rewrite associativity. rewrite <- H22. assumption.
  Qed.

End Product.

Arguments AllProducts C : clear implicits.

Module ProductFunctor.
  Section ProductFunctor.
    Context {D C : PreCategory}.
    Context (F : Functor D (C * C)).
    Context (P : forall(d : object D), Product (fst (F _0 d)%object) (snd (F _0 d)%object)).

    Definition ProdFunctor : Functor D C.
    Proof.
      srapply Build_Functor.
      - intro d. exact (prod_obj (P d)).
      - intros s d m. simpl.
        exact (proj1 (product_ex _ _
                                 ((fst (F _1 m)) o pi1 (P s))
                                 ((snd (F _1 m)) o pi2 (P s)))).
      - intros s d1 d2 m1 m2; simpl.
        rewrite product_ex_comm. rewrite (composition_of F).
        rewrite associativity. rewrite associativity. reflexivity.
      - intro x; simpl. rewrite (identity_of F). simpl.
        destruct (product_ex _ _ (1 o pi1 _) (1 o pi2 _)) as [ eta [ H1 H2 ] ].
        apply product_uniq; simpl;
          [ rewrite <- H1 | rewrite <- H2 ];
          rewrite left_identity; rewrite right_identity;
          reflexivity.
    Defined.

  End ProductFunctor.
End ProductFunctor.

Definition ProdFunctor {C : PreCategory} (P : AllProducts C) : Functor (C * C) C :=
  ProductFunctor.ProdFunctor 1%functor (fun p => P (fst p) (snd p)).
Definition ProdRFunctor {C : PreCategory} (X : object C) (P : forall Y, Product Y X) : Functor C C :=
  ProductFunctor.ProdFunctor ((1, ! X) o ProductLaws.Law1.inverse C)%functor P.
Definition ProdLFunctor {C : PreCategory} (X : object C) (P : forall Y, Product X Y) : Functor C C :=
  ProductFunctor.ProdFunctor ((!X, 1) o ProductLaws.Law1.inverse' C)%functor P.
