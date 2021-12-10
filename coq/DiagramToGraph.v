
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
Require Import Misc.
Require Import Graph.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Local Open Scope morphism_scope.

Section DiagToGraph.
  Context `{Funext}.

  Definition DiagramToGraph {I C :  PreCategory} (D : Functor I C) : Graph C (object I) (Arrows I) :=
    {| gr_vertex := fun x => (D _0 x)%object
    ;  gr_edges  := fun m => {| proj1 := arr_src m
                          ;  proj2 := {| proj1 := arr_dst m
                                      ;  proj2 := D _1 (arr_mph m)
                                      |}
                          |}
    |}.

  Definition DiagConeToGraphCone {I C : PreCategory} (D : Functor I C) {c : object C} :
    NaturalTransformation (diagonal_functor' C I _0 c)%object D -> Cone (DiagramToGraph D).
  Proof.
    intro t. srapply mkCone; [ exact c | exact (components_of t) | idtac ].
    intro a. unfold DiagramToGraph; unfold gr_edge; unfold gr_src; unfold gr_dst; simpl.
    rewrite <- (right_identity C _ _ (t (arr_dst a))).
    destruct a as [ src dst m ]; simpl. apply (commutes_sym t src dst m).
  Defined.

  Definition DiagConeToGraphCone' {I C : PreCategory} (D : Functor I C) :
    forall(cn : Cone (DiagramToGraph D)),
      NaturalTransformation (diagonal_functor' C I _0 (cn_top cn))%object D.
  Proof.
    intro cn. srapply Build_NaturalTransformation; [ exact (cn_side cn) | idtac ].
    intros src dst m. simpl. rewrite right_identity.
    rewrite (cn_comm cn (mkArrow m)). reflexivity.
  Qed.

  Check IsLimit.

End DiagToGraph.
