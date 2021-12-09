
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
Require Import Graph.

Definition Arrows (C : PreCategory) : Type :=
  exists(a b : object C), morphism C a b.

Include FunctorCoreNotations.

Definition eq_to_iso {C : PreCategory} {x y : object C} (p : x = y) : morphism C x y.
Proof.
  rewrite p. exact 1%morphism.
Defined.

Local Open Scope morphism.

Record GraphDiagram {size arrows : nat} {C I : PreCategory}
       {D : Functor I C} {G : Graph C size arrows} :=
  mkGraphDiagram
    { ftgr_objs : Fin size -> object I
    ; ftgr_objs_equiv : IsEquiv ftgr_objs
    ; ftgr_vertices : Fin arrows -> Arrows I
    ; ftgr_vertices_equiv : IsEquiv ftgr_vertices
    ; ftgr_src_comm : forall(a : Fin arrows), ftgr_objs (gr_src G a) = proj1 (ftgr_vertices a)
    ; ftgr_dst_comm : forall(a : Fin arrows), ftgr_objs (gr_dst G a) = proj1 (proj2 (ftgr_vertices a))
    ; ftgr_objs_comm : forall(v : Fin size), (D _0 (ftgr_objs v))%object = gr_vertex G v
    ; ftgr_edge_comm : forall(a : Fin arrows), D _1 (proj2 (proj2 (ftgr_vertices a)))
                                          = D _1 (eq_to_iso (ftgr_dst_comm a))
                                            o eq_to_iso (ftgr_objs_comm (gr_dst G a))^
                                            o gr_edge G a
                                            o eq_to_iso (ftgr_objs_comm (gr_src G a))
                                            o D _1 (eq_to_iso (ftgr_src_comm a)^)
    }.

