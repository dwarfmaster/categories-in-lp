
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Categories.Comma.
From HoTT Require Import Spaces.Finite.
Require Import Misc.
Require Import Limits.Graph.
Require Import Limits.Product.
Require Import Limits.Terminal.
Require Import Limits.Pullback.
Require Import Limits.Extension.
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

    Context {C : PreCategory}.
    Context {LCC : IsLocallyCartesian C}.
    Context {LCCC : IsLocallyCartesianClosed LCC}.
    Let P : AllPullbacks C := LocallyCartesianHasPullbacks LCC.

    Context {X Y : object C}.
    Context (f : morphism C X Y).

    Definition FToP {E : object C} (p : morphism C E X) :
      ExponentialObject (Build_SliceObject (f o p)) (Build_SliceObject f) _ :=
      LCCC (Build_SliceObject (f o p)) (Build_SliceObject f).
    Definition sFToP {E : object C} (p : morphism C E X) : object C :=
      s (eobject (FToP p)).
    Definition FToF :
      ExponentialObject (Build_SliceObject f) (Build_SliceObject f) _ :=
      LCCC (Build_SliceObject f) (Build_SliceObject f).
    Definition sFToF : object C := s (eobject FToF).

    Definition m1 {E : object C} (p : morphism C E X) : morphism C (sFToP p) sFToF.
    Proof.
      apply m. apply (curry FToF).
      exact (Build_SliceMorphism (Build_SliceObject (f o p)) (Build_SliceObject f) p 1
                                 o (ev (FToP p))).
    Defined.
    Definition m2 : morphism C Y (sFToF).
    Proof.
      change Y with (s (Build_SliceObject (identity Y))).
      apply m. apply (curry FToF). apply pi2.
    Defined.

    Definition Pb (p : object (C/X)) : Pullback (m1 (Slice.f p)) m2 := P _ _ _ (m1 (Slice.f p)) m2.
    Definition PiOnObjs : object (C/X) -> object (C/Y) :=
      fun p => Build_SliceObject (fpi2 (Pb p)).

    Definition LiftMph {p1 p2 : object (C/X)} (mph : morphism (C/X) p1 p2) :
      morphism C (sFToP (Slice.f p1)) (sFToP (Slice.f p2)).
    Proof.
      apply m. apply (curry (FToP (Slice.f p2))).
      refine (Build_SliceMorphism (Build_SliceObject (f o Slice.f p1))
                                  (Build_SliceObject (f o Slice.f p2))
                                  (m mph) _
                                  o ev (FToP (Slice.f p1))).
      simpl. rewrite associativity. f_ap. apply slice_m_comm.
    Defined.
    Lemma LiftMphComm {p1 p2 : object (C/X)} (mph : morphism (C/X) p1 p2) :
      m1 (Slice.f p2) o LiftMph mph = m1 (Slice.f p1).
    Proof.
      symmetry. rewrite <- slice_m_comp. unfold m1. f_ap. apply curry_uniq. rewrite composition_of.
      rewrite <- (associativity _ _ _ _ _ _ _ (ev FToF)). rewrite curry_comm.
      rewrite (associativity _ _ _ _ _ _ (ev (FToP (Slice.f p2)))). rewrite curry_comm.
      rewrite <- (associativity _ _ _ _ _ (ev (FToP (Slice.f p1)))). f_ap.
      apply slice_m_injective. rewrite slice_m_comp. simpl. apply slice_m_comm.
    Qed.
    Lemma LiftMphComp {p1 p2 p3 : object (C/X)}
          (mph1 : morphism (C/X) p1 p2) (mph2 : morphism (C/X) p2 p3) :
      LiftMph (mph2 o mph1) = LiftMph mph2 o LiftMph mph1.
    Proof.
      unfold LiftMph. rewrite <- slice_m_comp. f_ap. apply curry_uniq.
      rewrite composition_of. rewrite <- (associativity _ _ _ _ _ _ _ (ev _)).
      rewrite curry_comm. rewrite (associativity _ _ _ _ _ _ (ev _)).
      rewrite curry_comm. rewrite <- (associativity _ _ _ _ _ (ev _)). f_ap.
      apply slice_m_injective. rewrite slice_m_comp. reflexivity.
    Qed.
    Lemma LiftMphId (p : object (C/X)) : LiftMph (identity p) = 1.
    Proof.
      rewrite <- slice_m_id. unfold LiftMph. f_ap. apply curry_uniq.
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
      - intro n; destruct2 n; unfold gr_edge; simpl; [ | reflexivity ].
        rewrite <- associativity. rewrite LiftMphComm.
        rewrite (cn_comm (lim_cone (Pb p1)) fin1).
        rewrite (cn_comm (lim_cone (Pb p1)) fin2).
        reflexivity.
    Defined.
    Definition p1_cone_morphism {p1 p2 : object (C/X)} (mph : morphism (C/X) p1 p2) :
      ConeMorphism (p1_cone mph) (lim_cone (Pb p2)) :=
      lim_ex (Pb p2) (p1_cone mph).

    Definition PiOnMphs {a b : object (C/X)} :
      morphism (C/X) a b -> morphism (C/Y) (PiOnObjs a) (PiOnObjs b).
    Proof.
      intro mph. refine (Build_SliceMorphism (PiOnObjs a) (PiOnObjs b)
                                             (cnmph_mph (p1_cone_morphism mph)) _).
      simpl. rewrite (cnmph_comm (p1_cone_morphism mph) f2). reflexivity.
    Defined.
    Lemma PiOnMphsComp {a b c : object (C/X)}
          (mph1 : morphism (C/X) a b) (mph2 : morphism (C/X) b c) :
      PiOnMphs (mph2 o mph1) = PiOnMphs mph2 o PiOnMphs mph1.
    Proof.
      apply slice_m_injective. rewrite slice_m_comp. simpl (m _ o m _).
      change (m (PiOnMphs (mph2 o mph1))) with (cnmph_mph (p1_cone_morphism (mph2 o mph1))).
      pose (mph1_comm := cnmph_comm (p1_cone_morphism mph1)).
      pose (mph2_comm := cnmph_comm (p1_cone_morphism mph2)).
      refine (fprod_uniq (Pb c) _ _ _ _).
      - rewrite <- associativity. rewrite (mph2_comm f1). simpl (cn_side _ _).
        rewrite associativity.   rewrite (mph1_comm f1). simpl (cn_side _ _).
        rewrite (cnmph_comm (p1_cone_morphism (mph2 o mph1)) f1).
        change (cn_side (p1_cone (mph2 o mph1)) f1)
          with (LiftMph (mph2 o mph1) o cn_side (lim_cone (Pb a)) f1).
        rewrite <- associativity. f_ap. apply LiftMphComp.
      - rewrite <- associativity. rewrite (mph2_comm f2). simpl (cn_side _ _).
        rewrite (mph1_comm f2). simpl (cn_side _ _).
        rewrite (cnmph_comm (p1_cone_morphism (mph2 o mph1)) f2).
        reflexivity.
    Qed.
    Lemma PiOnMphsId {a : object (C/X)} :
      PiOnMphs (identity a) = identity (PiOnObjs a).
    Proof.
      pose (mph := p1_cone_morphism (identity a)).
      apply slice_m_injective; simpl. refine (fprod_uniq (Pb a) _ _ _ _).
      - rewrite (cnmph_comm mph f1). rewrite right_identity. simpl.
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

  End DependentProduct.
End DependentProduct.
