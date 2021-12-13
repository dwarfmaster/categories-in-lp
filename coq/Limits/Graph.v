
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
Require Import Misc.

Local Open Scope morphism_scope.

Record Graph {C : PreCategory} {Size Arrows : Type} :=
  mkGraph
    { gr_vertex : Size -> object C
    ; gr_edges : Arrows
               -> exists(src dst : Size), morphism C (gr_vertex src) (gr_vertex dst)
    }.
Arguments Graph C : clear implicits.

Definition gr_src {C : PreCategory} {S A : Type} (G : Graph C S A) (n : A) : S :=
  proj1 (gr_edges G n).
Definition gr_dst {C : PreCategory} {S A : Type} (G : Graph C S A) (n : A) : S :=
  proj1 (proj2 (gr_edges G n)).
Definition gr_src' {C : PreCategory} {S A : Type} (G : Graph C S A) (n : A) : object C :=
  gr_vertex G (gr_src G n).
Definition gr_dst' {C : PreCategory} {S A : Type} (G : Graph C S A) (n : A) : object C :=
  gr_vertex G (gr_dst G n).
Definition gr_edge {C : PreCategory} {S A : Type} (G : Graph C S A) (n : A)
  : morphism C (gr_src' G n) (gr_dst' G n) :=
  proj2 (proj2 (gr_edges G n)).

Record Cone {C : PreCategory} {Size Arrows : Type} {G : Graph C Size Arrows} :=
  mkCone
    { cn_top  : object C
    ; cn_side : forall(n : Size), morphism C cn_top (gr_vertex G n)
    ; cn_comm : forall(a : Arrows), gr_edge G a o cn_side (gr_src G a) = cn_side (gr_dst G a)
    }.
Arguments Cone {C Size Arrows} G.
Record ConeMorphism {C : PreCategory} {Size Arrows : Type} {G : Graph C Size Arrows} {c1 c2 : Cone G} :=
  mkCnMph
    { cnmph_mph  : morphism C (cn_top c1) (cn_top c2)
    ; cnmph_comm : forall(n : Size), cn_side c2 n o cnmph_mph = cn_side c1 n
    }.
Arguments ConeMorphism {C Size Arrows G} c1 c2.
Record Limit {C : PreCategory} {Size Arrows : Type} {G : Graph C Size Arrows} :=
  mkLim
    { lim_cone : Cone G
    ; lim_ex   : forall(c : Cone G), ConeMorphism c lim_cone
    ; lim_uniq : forall(c : Cone G), forall(m1 m2 : ConeMorphism c lim_cone), cnmph_mph m1 = cnmph_mph m2
    }.
Arguments Limit {C Size Arrows} G.

Definition HasFiniteLimits (C : PreCategory) :=
  forall(size arrows : nat), forall(G : Graph C (Fin size) (Fin arrows)), Limit G.
