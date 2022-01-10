
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import EquivGroupoids.
From HoTT Require Import Spaces.Finite.
From HoTT Require Import Types.Equiv.
From HoTT Require Import Types.Forall.
Require Import Misc.
Require Import Limits.Graph.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section GraphCategory.
  Context `{Funext}.
  Context (C : PreCategory).

  Definition eqToIso {A B : object C} : A = B -> morphism C A B :=
    fun p => p # 1.

  Definition shift_morphism {A1 A2 B1 B2 : object C} (pA : A2 = A1) (pB : B1 = B2) :
    morphism C A1 B1 -> morphism C A2 B2 :=
    fun m => eqToIso pB o m o eqToIso pA.

  Record GraphMorphism {S1 S2 A1 A2 : Type} (G1 : Graph C S1 A1) (G2 : Graph C S2 A2) :=
    Build_GraphMorphism
      { grmph_vertex_equiv : S1 <~> S2
      ; grmph_arrows_equiv : A1 <~> A2
      ; grmph_src_eq : forall(a : A1), equiv_fun grmph_vertex_equiv (gr_src G1 a)
                                  = gr_src G2 (equiv_fun grmph_arrows_equiv a)
      ; grmph_dst_eq : forall(a : A1), gr_dst G2 (equiv_fun grmph_arrows_equiv a)
                                  = equiv_fun grmph_vertex_equiv (gr_dst G1 a)
      ; grmph_mph : forall(v : S1), morphism C (gr_vertex G1 v)
                                        (gr_vertex G2 (equiv_fun grmph_vertex_equiv v))
      ; grmph_nat : forall(a : A1), grmph_mph (gr_dst G1 a)
                                 o gr_edge G1 a
                               = shift_morphism
                                   (ap (gr_vertex G2) (grmph_src_eq a))
                                   (ap (gr_vertex G2) (grmph_dst_eq a))
                                   (gr_edge G2 (equiv_fun grmph_arrows_equiv a))
                                 o grmph_mph (gr_src G1 a)
      }.

  Record GraphObject :=
    Build_GraphObject
      { grobj_size : Type
      ; grobj_arrows : Type
      ; grobj_graph : Graph C grobj_size grobj_arrows
      }.

  Definition GraphIdentity {Size Arrows : Type} (G : Graph C Size Arrows) :
    GraphMorphism G G.
  Proof.
    srapply Build_GraphMorphism.
    - exact (equiv_idmap Size).
    - exact (equiv_idmap Arrows).
    - intro a. reflexivity.
    - intro a. reflexivity.
    - intro v. exact 1.
    - intro a. unfold shift_morphism. simpl.
      repeat rewrite left_identity. repeat rewrite right_identity. reflexivity.
  Defined.

  Definition GraphComposition {S1 S2 S3 A1 A2 A3 : Type}
             {G1 : Graph C S1 A1} {G2 : Graph C S2 A2} {G3 : Graph C S3 A3}
             (mph2 : GraphMorphism G2 G3) (mph1 : GraphMorphism G1 G2) :
    GraphMorphism G1 G3.
  Proof.
    srapply Build_GraphMorphism.
    - exact (equiv_compose' (grmph_vertex_equiv mph2) (grmph_vertex_equiv mph1)).
    - exact (equiv_compose' (grmph_arrows_equiv mph2) (grmph_arrows_equiv mph1)).
    - intro a. exact (ap (grmph_vertex_equiv mph2) (grmph_src_eq mph1 a)
                     @ grmph_src_eq mph2 (grmph_arrows_equiv mph1 a)).
    - intro a. exact (grmph_dst_eq mph2 (grmph_arrows_equiv mph1 a)
                     @ ap (grmph_vertex_equiv mph2) (grmph_dst_eq mph1 a)).
    - intro v. simpl. exact (grmph_mph mph2 (grmph_vertex_equiv mph1 v) o grmph_mph mph1 v).
    - intro a. simpl. rewrite associativity. rewrite grmph_nat. rewrite <- associativity.
      unfold shift_morphism; simpl. destruct (grmph_dst_eq mph1 a); simpl.
      rewrite left_identity. rewrite <- associativity. rewrite grmph_nat.
      unfold shift_morphism; simpl. rewrite <- associativity. f_ap. rewrite concat_p1.
      repeat rewrite associativity. f_ap. f_ap.
      destruct (grmph_src_eq mph2 (grmph_arrows_equiv mph1 a)); simpl.
      rewrite left_identity. destruct (grmph_src_eq mph1 a); simpl.
      rewrite left_identity. rewrite right_identity. reflexivity.
  Defined.

  Lemma path_GraphMorphism {S1 S2 A1 A2 : Type} {G1 : Graph C S1 A1} {G2 : Graph C S2 A2}
        (HS2 : IsHSet S2) (mph1 mph2 : GraphMorphism G1 G2) :
    forall(p_vertex : equiv_fun (grmph_vertex_equiv mph1) = equiv_fun (grmph_vertex_equiv mph2)),
    forall(p_arrows : equiv_fun (grmph_arrows_equiv mph1) = equiv_fun (grmph_arrows_equiv mph2)),
    (forall v, grmph_mph mph1 v
          = eqToIso (ap (fun eq => gr_vertex G2 (equiv_fun eq v)) (path_equiv p_vertex)^)
            o grmph_mph mph2 v)
    -> mph1 = mph2.
  Proof.
    destruct mph1; destruct mph2; simpl. intros p_vertex p_arrows p_mph.
    generalize dependent grmph_nat1. generalize dependent grmph_nat0.
    generalize dependent grmph_src_eq1. generalize dependent grmph_src_eq0.
    generalize dependent grmph_dst_eq1. generalize dependent grmph_dst_eq0.
    generalize dependent p_mph.
    generalize dependent grmph_mph0. generalize dependent grmph_mph1.
    destruct (path_equiv p_vertex). clear p_vertex.
    destruct (path_equiv p_arrows). clear p_arrows.
    simpl. intros grmph_mph1 grmph_mph0 p_mph.
    assert (grmph_mph0 = grmph_mph1) as Hmph.
    { apply path_forall. intro v. rewrite p_mph. apply left_identity. }
    rewrite <- Hmph. clear grmph_mph1 p_mph Hmph.
    intros dst_eq0 dst_eq1 src_eq0 src_eq1.
    assert (dst_eq0 = dst_eq1) as Hdst.
    { apply path_forall. intro a. apply hset_has_UIP. assumption. }
    rewrite <- Hdst. clear dst_eq1 Hdst.
    assert (src_eq0 = src_eq1) as Hsrc.
    { apply path_forall. intro a. apply hset_has_UIP. assumption. }
    rewrite <- Hsrc. clear src_eq1 HS2 Hsrc.
    intros grmph_nat0 grmph_nat1. f_ap. apply path_forall. intro a.
    apply hset_has_UIP. apply trunc_morphism.
  Qed.

  Lemma GraphComp_left_identity {S1 A1 S2 A2 : Type} (HS2 : IsHSet S2)
        {G1 : Graph C S1 A1} {G2 : Graph C S2 A2} (m : GraphMorphism G1 G2) :
    GraphComposition (GraphIdentity G2) m = m.
  Proof.
    srapply path_GraphMorphism; simpl.
    - apply path_forall. reflexivity.
    - apply path_forall. reflexivity.
    - intro v. rewrite path_forall_1. unfold path_equiv.
      destruct m. repeat simpl (grmph_vertex_equiv _). repeat simpl (grmph_mph _).
      destruct grmph_vertex_equiv0. simpl.
      repeat rewrite concat_1p. repeat rewrite concat_p1.
      change (fun x => equiv_fun x) with equiv_fun. change isequiv_compose with equiv_isequiv.
      rewrite (Sigma.path_sigma_hprop_1 (equiv_fun; isequiv_compose)).
      assert (equiv_path_equiv (1 oE grmph_vertex_equiv m) (grmph_vertex_equiv m) idpath
              = idpath (equiv_fun (grmph_vertex_equiv m))).
      change (1 oE grmph_vertex_equiv m) with (grmph_vertex_equiv m). rewrite path_equiv_1.


End GraphCategory.
