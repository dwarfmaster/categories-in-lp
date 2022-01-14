
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Categories.Category.Morphisms.
From HoTT Require Import Categories.Comma.
From HoTT Require Import Spaces.Finite.
From HoTT Require Import Categories.Adjoint.UnitCounit.
From HoTT Require Import Categories.Adjoint.UnitCounitCoercions.
From HoTT Require Import Categories.Adjoint.Hom.
From HoTT Require Import Categories.Adjoint.HomCoercions.
Require Import Misc.
Require Import Limits.Graph.
Require Import Limits.Product.
Require Import Limits.Terminal.
Require Import Limits.Pullback.
Require Import Limits.Extension.
Require Import Limits.Functor.
Require Import Slice.Misc.
Require Import Slice.BaseChangeFunctor.
Require Import Cartesian.
Require Import Exponential.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Definition IsCartesianClosed {C : PreCategory} (P : IsCartesian C) :=
  AllExponentials (snd P).

Definition IsLocallyCartesianClosed {C : PreCategory} (P : IsLocallyCartesian C) :=
  forall(a : object C), IsCartesianClosed (P a).

Module DependentProduct.
  Section DependentProduct.
    Import Slice.
    Context `{Funext}.

    Context {C : PreCategory}.
    Context {LCC : IsLocallyCartesian C}.
    Context {LCCC : IsLocallyCartesianClosed LCC}.

    Context {X Y : object C}.
    Context (f : morphism C X Y).
    Print LCCHasLocalPullbacks.
    Let P : AllPullbacks (C/Y) := LCCHasLocalPullbacks LCC Y.

    Definition FToP {E : object C} (p : morphism C E X) :
      ExponentialObject (Build_SliceObject (f o p)) (Build_SliceObject f) _ :=
      LCCC (Build_SliceObject (f o p)) (Build_SliceObject f).
    Definition sFToP {E : object C} (p : morphism C E X) : object (C/Y) :=
      eobject (FToP p).
    Definition FToF :
      ExponentialObject (Build_SliceObject f) (Build_SliceObject f) _ :=
      LCCC (Build_SliceObject f) (Build_SliceObject f).
    Definition sFToF : object (C/Y) := eobject FToF.

    Definition m1 {E : object C} (p : morphism C E X) :
      morphism (C/Y) (sFToP p) sFToF.
    Proof.
      apply (curry FToF).
      exact (Build_SliceMorphism (Build_SliceObject (f o p)) (Build_SliceObject f) p 1
                                 o (ev (FToP p))).
    Defined.
    Definition m2 : morphism (C/Y) (Build_SliceObject 1) sFToF.
    Proof.
      change Y with (s (Build_SliceObject (identity Y))).
      apply (curry FToF). apply pi2.
    Defined.

    Definition Pb (p : object (C/X)) : Pullback (m1 (Slice.f p)) m2 := P (m1 (Slice.f p)) m2.
    Definition PiOnObjs : object (C/X) -> object (C/Y) :=
      fun p => fprod_obj (Pb p).

    Definition LiftMph {p1 p2 : object (C/X)} (mph : morphism (C/X) p1 p2) :
      morphism (C/Y) (sFToP (Slice.f p1)) (sFToP (Slice.f p2)).
    Proof.
      apply (curry (FToP (Slice.f p2))).
      refine (Build_SliceMorphism (Build_SliceObject (f o Slice.f p1))
                                  (Build_SliceObject (f o Slice.f p2))
                                  (m mph) _
                                  o ev (FToP (Slice.f p1))).
      simpl. rewrite associativity. f_ap. apply slice_m_comm.
    Defined.
    Lemma LiftMphComm {p1 p2 : object (C/X)} (mph : morphism (C/X) p1 p2) :
      m1 (Slice.f p2) o LiftMph mph = m1 (Slice.f p1).
    Proof.
      symmetry. unfold m1. apply curry_uniq. rewrite composition_of.
      rewrite <- (associativity _ _ _ _ _ _ _ (ev FToF)). rewrite curry_comm.
      rewrite (associativity _ _ _ _ _ _ (ev (FToP (Slice.f p2)))). rewrite curry_comm.
      rewrite <- (associativity _ _ _ _ _ (ev (FToP (Slice.f p1)))). f_ap.
      apply slice_m_injective. rewrite slice_m_comp. simpl. apply slice_m_comm.
    Qed.
    Lemma LiftMphComp {p1 p2 p3 : object (C/X)}
          (mph1 : morphism (C/X) p1 p2) (mph2 : morphism (C/X) p2 p3) :
      LiftMph (mph2 o mph1) = LiftMph mph2 o LiftMph mph1.
    Proof.
      unfold LiftMph. apply curry_uniq.
      rewrite composition_of. rewrite <- (associativity _ _ _ _ _ _ _ (ev _)).
      rewrite curry_comm. rewrite (associativity _ _ _ _ _ _ (ev _)).
      rewrite curry_comm. rewrite <- (associativity _ _ _ _ _ (ev _)). f_ap.
      apply slice_m_injective. rewrite slice_m_comp. reflexivity.
    Qed.
    Lemma LiftMphId (p : object (C/X)) : LiftMph (identity p) = 1.
    Proof.
      unfold LiftMph. apply curry_uniq.
      rewrite identity_of. rewrite right_identity. apply slice_m_injective.
      rewrite slice_m_comp. simpl. rewrite left_identity. reflexivity.
    Qed.

    Definition p1_cone {p1 p2 : object (C/X)} (mph : morphism (C/X) p1 p2) :
      Cone (PullbackGr (m1 (Slice.f p2)) m2).
    Proof.
      srapply mkCone; [ exact (cn_top (lim_cone (Pb p1))) | | ].
      - intro n; destruct3 n.
        + exact (m2 o (cn_side (lim_cone (Pb p1)) f2)).
        + exact (cn_side (lim_cone (Pb p1)) f2).
        + exact (LiftMph mph o (cn_side (lim_cone (Pb p1)) f1)).
      - intro n; apply slice_m_injective; destruct2 n; unfold gr_edge; simpl; [ | reflexivity ].
        rewrite <- associativity. rewrite <- (slice_m_comp (LiftMph mph) (m1 (Slice.f p2))).
        rewrite LiftMphComm.
        rewrite <- (slice_m_comp (cn_side (lim_cone (Pb p1)) f1) (m1 (Slice.f p1))).
        rewrite (cn_comm (lim_cone (Pb p1)) fin2).
        rewrite <- (slice_m_comp (cn_side (lim_cone (Pb p1)) f2) m2).
        rewrite (cn_comm (lim_cone (Pb p1)) fin1).
        reflexivity.
    Defined.
    Definition p1_cone_morphism {p1 p2 : object (C/X)} (mph : morphism (C/X) p1 p2) :
      ConeMorphism (p1_cone mph) (lim_cone (Pb p2)) :=
      lim_ex (Pb p2) (p1_cone mph).

    Definition PiOnMphs {a b : object (C/X)} :
      morphism (C/X) a b -> morphism (C/Y) (PiOnObjs a) (PiOnObjs b).
    Proof.
      intro mph. refine (cnmph_mph (p1_cone_morphism mph)).
    Defined.
    Lemma PiOnMphsComp {a b c : object (C/X)}
          (mph1 : morphism (C/X) a b) (mph2 : morphism (C/X) b c) :
      PiOnMphs (mph2 o mph1) = PiOnMphs mph2 o PiOnMphs mph1.
    Proof.
      change (PiOnMphs (mph2 o mph1)) with (cnmph_mph (p1_cone_morphism (mph2 o mph1))).
      pose (mph1_comm := cnmph_comm (p1_cone_morphism mph1)).
      pose (mph2_comm := cnmph_comm (p1_cone_morphism mph2)).
      refine (fprod_uniq (Pb c) _ _ _ _).
      - rewrite <- associativity. rewrite (mph2_comm f1).
        rewrite associativity.   rewrite (mph1_comm f1).
        rewrite (cnmph_comm (p1_cone_morphism (mph2 o mph1)) f1).
        change (cn_side (p1_cone (mph2 o mph1)) f1)
          with (LiftMph (mph2 o mph1) o cn_side (lim_cone (Pb a)) f1).
        rewrite <- associativity. f_ap. apply LiftMphComp.
      - rewrite <- associativity. rewrite (mph2_comm f2).
        rewrite (mph1_comm f2).
        rewrite (cnmph_comm (p1_cone_morphism (mph2 o mph1)) f2).
        reflexivity.
    Qed.
    Lemma PiOnMphsId {a : object (C/X)} :
      PiOnMphs (identity a) = identity (PiOnObjs a).
    Proof.
      pose (mph := p1_cone_morphism (identity a)). refine (fprod_uniq (Pb a) _ _ _ _).
      - rewrite (cnmph_comm mph f1). rewrite right_identity.
        change (cn_side (p1_cone 1) f1) with (LiftMph 1 o (cn_side (lim_cone (Pb a)) f1)).
        rewrite LiftMphId. apply left_identity.
      - rewrite (cnmph_comm mph f2). rewrite right_identity. reflexivity.
    Qed.

    Definition DependentProduct : Functor (C/X) (C/Y).
    Proof.
      srapply Build_Functor.
      - exact PiOnObjs.
      - intros s d. apply PiOnMphs.
      - intros s d d' m1 m2. apply PiOnMphsComp.
      - intro x. apply PiOnMphsId.
    Defined.

    Section AlternativeBaseChangeFunctor.
      (* I must define the base change functor in an alternative way, in order
       to get some equalities definitionally. Afterwards I prove it is naturally
       isomorphic to the usual BaseChangeFunctor *)

      Definition fob := Build_SliceObject f.
      Definition BCObjs : object (C/Y) -> object (C/X) :=
        fun m => Build_SliceObject (Slice.m (pi1 (snd (LCC Y) fob m))).
      Definition BCMph {s d : object (C/Y)} :
        morphism (C/Y) s d -> morphism (C/X) (BCObjs s) (BCObjs d).
      Proof.
        intro g. pose (sprod := snd (LCC Y) fob s). pose (dprod := snd (LCC Y) fob d).
        destruct (product_ex dprod (prod_obj sprod) (pi1 sprod) (g o pi2 sprod))
                 as [ mph [ Hmph1 Hmph2 ] ].
        srapply Build_SliceMorphism; [ exact (Slice.m mph) | simpl ].
        rewrite Hmph1. rewrite slice_m_comp. reflexivity.
      Defined.

      Definition BC : Functor (C/Y) (C/X).
      Proof.
        srapply Build_Functor; [ exact BCObjs | exact (fun s d m => BCMph m) | | ].
        - intros s d d' m3 m4. apply slice_m_injective. rewrite slice_m_comp. simpl.
          rewrite <- slice_m_comp. f_ap. apply product_uniq.
          + rewrite <- associativity.
            rewrite <- (fst (product_ex (snd (LCC Y) fob d') (prod_obj (snd (LCC Y) fob s))
                                       (pi1 (snd (LCC Y) fob s))
                                       (m4 o m3 o pi2 (snd (LCC Y) fob s))).2).
            rewrite <- (fst (product_ex (snd (LCC Y) fob d') (prod_obj (snd (LCC Y) fob d))
                                       (pi1 (snd (LCC Y) fob d))
                                       (m4 o pi2 (snd (LCC Y) fob d))).2).
            rewrite <- (fst (product_ex (snd (LCC Y) fob d) (prod_obj (snd (LCC Y) fob s))
                                       (pi1 (snd (LCC Y) fob s))
                                       (m3 o pi2 (snd (LCC Y) fob s))).2).
            reflexivity.
          + rewrite <- associativity.
            rewrite <- (snd (product_ex (snd (LCC Y) fob d') (prod_obj (snd (LCC Y) fob s))
                                       (pi1 (snd (LCC Y) fob s))
                                       (m4 o m3 o pi2 (snd (LCC Y) fob s))).2).
            rewrite <- (snd (product_ex (snd (LCC Y) fob d') (prod_obj (snd (LCC Y) fob d))
                                       (pi1 (snd (LCC Y) fob d))
                                       (m4 o pi2 (snd (LCC Y) fob d))).2).
            rewrite associativity. rewrite associativity.
            rewrite <- (snd (product_ex (snd (LCC Y) fob d) (prod_obj (snd (LCC Y) fob s))
                                       (pi1 (snd (LCC Y) fob s))
                                       (m3 o pi2 (snd (LCC Y) fob s))).2).
            reflexivity.
        - intro x. apply slice_m_injective. rewrite slice_m_id. simpl.
          rewrite <- slice_m_id. f_ap. apply product_uniq.
          + rewrite <- (fst (product_ex (snd (LCC Y) fob x) (prod_obj (snd (LCC Y) fob x))
                                       (pi1 (snd (LCC Y) fob x))
                                       (1 o pi2 (snd (LCC Y) fob x))).2).
            rewrite right_identity. reflexivity.
          + rewrite <- (snd (product_ex (snd (LCC Y) fob x) (prod_obj (snd (LCC Y) fob x))
                                       (pi1 (snd (LCC Y) fob x))
                                       (1 o pi2 (snd (LCC Y) fob x))).2).
            rewrite right_identity. apply left_identity.
      Defined.

      (* TODO show that BC is naturally isomorphic to BaseChangeFunctor *)
    End AlternativeBaseChangeFunctor.

    Let DP := DependentProduct.

    Section DPAdjunctionPointwise.
      Context (p : object (C/X)) (m : object (C/Y)).
      Print Product.
      Let fob := Build_SliceObject f.
      Let fpob := Build_SliceObject (f o Slice.f p).
      Definition mXf : Product fob m := snd (LCC Y) fob m.
      Definition mXfTOfop : object set_cat := Build_HSet (morphism (C/Y) (prod_obj mXf) fpob).
      Definition mXfTOf : object set_cat := Build_HSet (morphism (C/Y) (prod_obj mXf) fob).
      Definition mTOid : object set_cat := Build_HSet (morphism (C/Y) m (Build_SliceObject 1)).
      Definition p_post : morphism set_cat mXfTOfop mXfTOf :=
        fun g => Build_SliceMorphism fpob fob (Slice.f p) 1 o g.
      Definition pi_m_const : morphism set_cat mTOid mXfTOf := fun _ => pi1 mXf.

      Definition HomSetGr := PullbackGr p_post pi_m_const.
      Definition bcmTOp : object set_cat := Build_HSet (morphism (C/X) (BC _0 m)%object p).
      Definition mTOdpp : object set_cat := Build_HSet (morphism (C/Y) m (DP _0 p)%object).

      Lemma ProductIsBaseChangeDiagonal :
          Slice.f (prod_obj mXf) = f o (Slice.f (BC _0 m)).
      Proof.
        simpl. change f with (Slice.f fob). change DependentProduct.fob with fob.
        rewrite (slice_m_comm (pi1 (snd (LCC Y) fob m))). reflexivity.
      Qed.

      Definition bcmTOpCone : Cone HomSetGr.
      Proof.
        srapply mkCone; [ exact bcmTOp | | ].
        - intro n; destruct3 n; intro g.
          + refine (p_post _).
            srapply Build_SliceMorphism; [ exact (Slice.m g) | ].
            simpl. rewrite associativity. rewrite (slice_m_comm g).
            rewrite ProductIsBaseChangeDiagonal. reflexivity.
          + srapply Build_SliceMorphism; [ exact (Slice.f m) | apply left_identity ].
          + srapply Build_SliceMorphism; [ exact (Slice.m g) | ].
            simpl. rewrite associativity. rewrite (slice_m_comm g).
            rewrite ProductIsBaseChangeDiagonal. reflexivity.
        - intro n; destruct2 n; apply path_forall; intro x; apply slice_m_injective; simpl;
            [ reflexivity | ].
          unfold gr_edge; simpl. unfold pi_m_const; simpl.
          rewrite (slice_m_comm x). reflexivity.
      Defined.

      Lemma bcmTOpConeInjective (m1 m2 : bcmTOp) :
        cn_side bcmTOpCone f1 m1 = cn_side bcmTOpCone f1 m2 -> m1 = m2.
      Proof. intro Heq. apply slice_m_injective. exact (ap Slice.m Heq). Qed.

      Definition bcmLimit : Limit HomSetGr.
      Proof.
        srapply mkLim; [ exact bcmTOpCone | | ].
        - intro c. srapply mkCnMph; [ | intro n; destruct3 n ]; simpl.
          + intro x. srapply Build_SliceMorphism; [ exact (Slice.m (cn_side c f1 x)) | ].
            pose (mp := gr_edge HomSetGr fin2 o cn_side c f1).
            change (Slice.f p o Slice.m (cn_side c f1 x)) with (Slice.m (mp x)).
            unfold mp. clear mp. rewrite (cn_comm c fin2).
            simpl. f_ap. change (gr_dst HomSetGr fin2) with f3.
            rewrite <- (cn_comm c fin1). reflexivity.
          + apply path_forall; intro x; apply slice_m_injective; simpl.
            pose (mp := gr_edge HomSetGr fin2 o cn_side c f1).
            change (Slice.f p o Slice.m (cn_side c f1 x)) with (Slice.m (mp x)).
            unfold mp. clear mp. rewrite (cn_comm c fin2).
            reflexivity.
          + apply path_forall; intro x; apply slice_m_injective; simpl.
            rewrite <- (slice_m_comm (cn_side c f2 x)); simpl.
            apply left_identity.
          + apply path_forall; intro x; apply slice_m_injective; simpl. reflexivity.
        - intros c m3 m4. apply path_forall; intro x; apply bcmTOpConeInjective.
          change (cn_side bcmTOpCone f1 (cnmph_mph m3 x))
            with ((cn_side bcmTOpCone f1 o cnmph_mph m3) x).
          change (cn_side bcmTOpCone f1 (cnmph_mph m4 x))
            with ((cn_side bcmTOpCone f1 o cnmph_mph m4) x).
          rewrite cnmph_comm. rewrite cnmph_comm. reflexivity.
      Defined.

      Definition HomM : Functor (C/Y) set_cat := covariant_hom_functor (C/Y) m.
      Definition AltHomSetGr := graph_of HomM (PullbackGr (m1 (Slice.f p)) m2).

      Definition isoCurry (over : object (C/Y)):
        morphism set_cat
                 (Build_HSet (morphism (C/Y) m (eobject (LCCC over fob))))
                 (Build_HSet (morphism (C/Y) (prod_obj mXf) over)) :=
        fun mslice => (curry_mph m (LCCC over fob))^-1 mslice o prod_swap_mph _ _.
      Local Instance isoCurryRIso (over : object (C/Y)) : IsIsomorphism (isoCurry over).
      Proof.
        srapply Build_IsIsomorphism.
        - intro mslice. refine (curry_mph m (LCCC over fob) _).
          refine (mslice o prod_swap_mph _ _).
        - apply path_forall; intro mslice. unfold isoCurry.
          simpl (@compose set_cat). cbn beta. rewrite associativity.
          rewrite prod_swap_invo. rewrite right_identity.
          change (curry_mph m (LCCC over fob) ((curry_mph m (LCCC over fob))^-1 mslice))
            with ((curry_mph m (LCCC over fob) o (curry_mph m (LCCC over fob))^-1) mslice).
          rewrite right_inverse. reflexivity.
        - apply path_forall; intro mslice. unfold isoCurry.
          simpl (@compose set_cat). cbn beta.
          change ((curry_mph m (LCCC over fob))^-1
                     (curry_mph m (LCCC over fob)
                       (mslice o prod_swap_mph (snd (LCC Y) m fob) mXf)))
            with (((curry_mph m (LCCC over fob))^-1 o curry_mph m (LCCC over fob))
                   (mslice o prod_swap_mph (snd (LCC Y) m fob) mXf)).
          rewrite left_inverse. simpl (@identity set_cat). cbn beta.
          rewrite associativity. rewrite prod_swap_invo. apply right_identity.
      Qed.
      Definition isoTop :
        morphism set_cat
                 (Build_HSet (morphism (C/Y) m (eobject (FToP (Slice.f p)))))
                 (Build_HSet (morphism (C/Y) (prod_obj mXf) fpob)) :=
        isoCurry fpob.
      Definition isoBottom :
        morphism set_cat
                 (Build_HSet (morphism (C/Y) m (eobject FToF)))
                 (Build_HSet (morphism (C/Y) (prod_obj mXf) fob)) :=
        isoCurry fob.
      Lemma isoSquareCommutes :
        p_post o isoTop = isoBottom o (HomM _1 (m1 (Slice.f p))).
      Proof.
        apply path_forall; intro mslice. simpl (@compose set_cat); cbn beta.
        unfold p_post; unfold HomM; unfold m1.
        change (((covariant_hom_functor (C / Y) m)
                 _1 (curry FToF
                   (Build_SliceMorphism (Build_SliceObject (f o Slice.f p)) (Build_SliceObject f)
                      (Slice.f p) 1 o ev (FToP (Slice.f p))))) mslice)
          with (curry FToF
                   (Build_SliceMorphism (Build_SliceObject (f o Slice.f p)) (Build_SliceObject f)
                      (Slice.f p) 1 o ev (FToP (Slice.f p))) o mslice o 1).
        rewrite right_identity. repeat rewrite <- associativity.
        unfold isoBottom; unfold isoCurry. simpl _^-1. unfold curry_inv_mph.
        unfold curry_inv. rewrite composition_of. rewrite <- associativity.
        rewrite curry_comm. reflexivity.
      Qed.
      Lemma isoSquareCommutes' :
        isoBottom^-1 o p_post = (HomM _1 (m1 (Slice.f p))) o isoTop^-1.
      Proof.
        apply iso_moveR_Vp. rewrite <- associativity. apply iso_moveL_pV.
        exact isoSquareCommutes.
      Qed.
      Lemma isoTriangleCommutes :
        isoBottom o (HomM _1 m2) = fun _ => pi1 mXf.
      Proof.
        apply path_forall; intro g. unfold m2; unfold HomM.
        simpl (@compose set_cat); cbn beta.
        change (((covariant_hom_functor (C / Y) m)
                 _1 (curry FToF (pi2 (snd (LCC Y) (Build_SliceObject 1) (Build_SliceObject f))))) g)
          with (curry FToF (pi2 (snd (LCC Y) (Build_SliceObject 1) (Build_SliceObject f))) o g o 1).
        rewrite right_identity. unfold isoBottom; unfold isoCurry.
        simpl _^-1. unfold curry_inv_mph; unfold curry_inv.
        rewrite composition_of. rewrite <- associativity.
        rewrite curry_comm. rewrite (ProdRFunctorPi2 fob (fun z => snd (LCC Y) z fob)).
        apply (snd (prod_swap _ _).2).
      Qed.
      Lemma isoTriangleCommutes' :
        HomM _1 m2 = isoBottom^-1 o (fun _ => pi1 mXf).
      Proof. apply iso_moveL_Vp. exact isoTriangleCommutes. Qed.

      Definition FromAltCone : Cone AltHomSetGr -> Cone HomSetGr.
      Proof.
        intro cn. srapply mkCone; [ exact (cn_top cn) | | ].
        - intro n; destruct3 n.
          + exact (isoBottom o cn_side cn f3).
          + exact (cn_side cn f2).
          + exact (isoTop o cn_side cn f1).
        - intro n; destruct2 n; apply path_forall; intro x; simpl (@compose set_cat); cbn beta.
          + rewrite <- (cn_comm cn fin2).
            change (isoBottom ((gr_edge AltHomSetGr fin2 o cn_side cn (gr_src AltHomSetGr fin2)) x))
              with ((isoBottom o (HomM _1 (m1 (Slice.f p)) o cn_side cn f1)) x).
            rewrite <- associativity. rewrite <- isoSquareCommutes.
            reflexivity.
          + rewrite <- (cn_comm cn fin1). change (gr_edge AltHomSetGr fin1) with (HomM _1 m2).
            change (isoBottom ((HomM _1 m2 o cn_side cn (gr_src AltHomSetGr fin1)) x))
              with ((isoBottom o (HomM _1 m2 o cn_side cn f2)) x).
            rewrite <- associativity. rewrite isoTriangleCommutes.
            reflexivity.
      Defined.
      Definition ToAltCone : Cone HomSetGr -> Cone AltHomSetGr.
      Proof.
        intro cn. srapply mkCone; [ exact (cn_top cn) | | ].
        - intro n; destruct3 n.
          + exact (isoBottom^-1 o cn_side cn f3).
          + exact (cn_side cn f2).
          + exact (isoTop^-1 o cn_side cn f1).
        - intro n; destruct2 n; apply path_forall; intro x; simpl (@compose set_cat); cbn beta.
          + rewrite <- (cn_comm cn fin2).
            change ((isoCurry fob)^-1 ((gr_edge HomSetGr fin2 o cn_side cn (gr_src HomSetGr fin2)) x))
              with ((isoBottom^-1 o (p_post o cn_side cn f1)) x).
            rewrite <- associativity. rewrite isoSquareCommutes'.
            reflexivity.
          + rewrite <- (cn_comm cn fin1). change (gr_edge HomSetGr fin1) with pi_m_const.
            change ((isoCurry fob)^-1 ((pi_m_const o cn_side cn (gr_src HomSetGr fin1)) x))
              with ((isoBottom^-1 o (pi_m_const o cn_side cn f2)) x).
            rewrite <- associativity. rewrite <- isoTriangleCommutes'.
            reflexivity.
      Defined.
      Definition ConeMorphismToAlt (c1 : Cone HomSetGr) (c2 : Cone AltHomSetGr) :
        ConeMorphism (ToAltCone c1) c2 ->
        ConeMorphism c1 (FromAltCone c2).
      Proof.
        intro mph. srapply mkCnMph; [ exact (cnmph_mph mph) | ].
        intro n; destruct3 n; apply path_forall; intro x; simpl (@compose set_cat); cbn beta.
        - change (isoBottom (cn_side c2 f3 (cnmph_mph mph x)))
            with ((isoBottom o (cn_side c2 f3 o cnmph_mph mph)) x).
          rewrite (cnmph_comm mph).
          change (cn_side (ToAltCone c1) f3) with (isoBottom^-1 o cn_side c1 f3).
          rewrite <- associativity. rewrite right_inverse. rewrite left_identity.
          reflexivity.
        - change (cn_side c2 f2 (cnmph_mph mph x)) with ((cn_side c2 f2 o cnmph_mph mph) x).
          rewrite (cnmph_comm mph f2). reflexivity.
        - change (isoTop (cn_side c2 f1 (cnmph_mph mph x)))
            with ((isoTop o (cn_side c2 f1 o cnmph_mph mph)) x).
          rewrite (cnmph_comm mph).
          change (cn_side (ToAltCone c1) f1) with (isoTop^-1 o cn_side c1 f1).
          rewrite <- associativity. rewrite right_inverse. rewrite left_identity.
          reflexivity.
      Defined.
      Definition ConeMorphismFromAlt (c1 : Cone HomSetGr) (c2 : Cone AltHomSetGr) :
        ConeMorphism c1 (FromAltCone c2) ->
        ConeMorphism (ToAltCone c1) c2.
      Proof.
        intro mph. srapply mkCnMph; [ exact (cnmph_mph mph) | ].
        intro n; destruct3 n; apply path_forall; intro x; simpl (@compose set_cat); cbn beta.
        - change ((isoCurry fob)^-1 (cn_side c1 f3 x)) with ((isoBottom^-1 o cn_side c1 f3) x).
          rewrite <- (cnmph_comm mph).
          change (cn_side (FromAltCone c2) f3) with (isoBottom o cn_side c2 f3).
          repeat rewrite <- associativity. rewrite left_inverse. rewrite left_identity.
          reflexivity.
        - change (cn_side c2 (inl (inr tt)) (cnmph_mph mph x))
            with ((cn_side c2 f2 o cnmph_mph mph) x).
          rewrite <- (cnmph_comm mph). reflexivity.
        - change ((isoCurry fpob)^-1 (cn_side c1 f1 x)) with ((isoTop^-1 o cn_side c1 f1) x).
          rewrite <- (cnmph_comm mph).
          change (cn_side (FromAltCone c2) f1) with (isoTop o cn_side c2 f1).
          repeat rewrite <- associativity. rewrite left_inverse. rewrite left_identity.
          reflexivity.
      Defined.
      Definition LimitFromAlt : Limit AltHomSetGr -> Limit HomSetGr.
      Proof.
        intro L. srapply mkLim; [ exact (FromAltCone (lim_cone L)) | | ].
        - intro c. apply ConeMorphismToAlt. apply lim_ex.
        - intros c m3 m4.
          pose (mph3 := ConeMorphismFromAlt m3). pose (mph4 := ConeMorphismFromAlt m4).
          apply (lim_uniq L _ mph3 mph4).
      Defined.

      Definition depLimit : Limit HomSetGr.
      Proof.
        apply LimitFromAlt. unfold AltHomSetGr. apply CovariantHomPreservesLimit. exact (Pb p).
      Defined.
    End DPAdjunctionPointwise.

    Theorem DPAdjunction : BC -| DependentProduct.
    Proof.
      apply adjunction_unit_counit__of__adjunction_unit.
      refine (adjunction_unit__of__adjunction_hom _).
      srapply Build_AdjunctionHom. admit.
    Admitted.

  End DependentProduct.
End DependentProduct.
