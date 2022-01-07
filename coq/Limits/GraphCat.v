
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
Require Import Misc.
Require Import Limits.Graph.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section GraphCategory.
  Context (C : PreCategory).

  Record GraphMorphism {S1 S2 A1 A2 : Type} (G1 : Graph C S1 A1) (G2 : Graph C S2 A2) :=
    Build_GraphMorphism
      { grmph_vertex_equiv : S1 <~> S2
      ; grmph_arrows_equiv : A1 <~> A2
      ; grmph_src_eq : forall(a : A1), equiv_fun grmph_vertex_equiv (gr_src G1 a)
                                  = gr_src G2 (equiv_fun grmph_arrows_equiv a)
      ; grmph_dst_eq : forall(a : A1), equiv_fun grmph_vertex_equiv (gr_dst G1 a)
                                  = gr_dst G2 (equiv_fun grmph_arrows_equiv a)
      ; grmph_mph : forall(v : S1), morphism C (gr_vertex G1 v)
                                        (gr_vertex G2 (equiv_fun grmph_vertex_equiv v))
      ; grmph_nat : forall(a : A1), (transport (fun x => morphism C (gr_dst' G1 a) (gr_vertex G2 x))
                                          (grmph_dst_eq a)
                                          (grmph_mph (gr_dst G1 a)))
                                 o gr_edge G1 a
                               = gr_edge G2 (equiv_fun grmph_arrows_equiv a)
                                 o (transport (fun x => morphism C (gr_src' G1 a) (gr_vertex G2 x))
                                              (grmph_src_eq a)
                                              (grmph_mph (gr_src G1 a)))
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
    - intro a. simpl. rewrite left_identity. rewrite right_identity. reflexivity.
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
    - intro a. exact (ap (grmph_vertex_equiv mph2) (grmph_dst_eq mph1 a)
                     @ grmph_dst_eq mph2 (grmph_arrows_equiv mph1 a)).
    - intro v. simpl. exact (grmph_mph mph2 (grmph_vertex_equiv mph1 v) o grmph_mph mph1 v).
    - intro a. simpl. rewrite transport_pp. rewrite transport_pp.
      rewrite <- transport_compose. rewrite <- transport_compose.

End GraphCategory.
