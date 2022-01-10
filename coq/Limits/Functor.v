
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

Section FunctorLimits.
  Local Open Scope object_scope.

  Context {C D : PreCategory}.
  Context (F : Functor C D).

  Context {Size Arrows : Type}.
  Context (G : Graph C Size Arrows).

  Definition graph_of : Graph D Size Arrows :=
    {| gr_vertex := fun s => (F _0 (gr_vertex G s))%object
    ;  gr_edges  := fun a => {| proj1 := gr_src G a
                          ;  proj2 :=
                            {| proj1 := gr_dst G a
                            ;  proj2 := F _1 (gr_edge G a)
                            |}
                          |}
    |}.

  Definition cone_of (cn : Cone G) : Cone graph_of.
  Proof.
    srapply mkCone; [ exact (F _0 (cn_top cn))%object
                    | intro side; exact (F _1 (cn_side cn side)) | ].
    intro a; unfold graph_of; unfold gr_edge; unfold gr_src; unfold gr_dst; simpl.
    rewrite <- composition_of. f_ap. apply cn_comm.
  Defined.

  Definition FunctorPreservesLimit :=
    forall(L : Limit G), exists(L' : Limit graph_of), lim_cone L' = cone_of (lim_cone L).
End FunctorLimits.

From HoTT Require Import Categories.Adjoint.UnitCounit.
From HoTT Require Import Categories.Adjoint.UnitCounitCoercions.
From HoTT Require Import Categories.Adjoint.Hom.
From HoTT Require Import Categories.Adjoint.HomCoercions.

Section AdjunctsPreserveLimits.
  Local Open Scope object_scope.

  Context {C D : PreCategory}.
  Context {F : Functor C D}.
  Context {G : Functor D C}.
  Context (Adj : F -| G).

  Context {Size Arrows : Type}.
  Context (Gr : Graph D Size Arrows).

  Definition counitCone :
    Cone (graph_of F (graph_of G Gr)) -> Cone Gr.
  Proof.
    intro cn. srapply mkCone; [ exact (cn_top cn) | | ].
    - intro n. refine (_ o cn_side cn n). simpl. apply (counit Adj).
    - intro a; simpl. rewrite <- (cn_comm cn a); simpl.
      unfold gr_edge; unfold gr_src; unfold gr_dst. simpl.
      unfold gr_edge; unfold gr_src; unfold gr_dst. simpl.
      repeat rewrite <- associativity. f_ap.
      rewrite (commutes (counit Adj)); simpl. reflexivity.
  Defined.

  Definition ConeMorphismLToR (cnC : Cone (graph_of G Gr)) (cnD : Cone Gr) :
    ConeMorphism (counitCone (cone_of F cnC)) cnD ->
    ConeMorphism cnC (cone_of G cnD).
  Proof.
    intro mph. srapply mkCnMph.
    - simpl. refine (equiv_fun (equiv_hom_set_adjunction _ _ _)^-1 _).
      + apply adjunction_unit__of__adjunction_unit_counit. exact Adj.
      + apply (cnmph_mph mph).
    - intro n. simpl. rewrite <- associativity. rewrite <- composition_of.
      rewrite (cnmph_comm mph); simpl. rewrite composition_of.
      rewrite associativity. rewrite <- (commutes (unit Adj)). simpl.
      rewrite <- associativity. rewrite unit_counit_equation_2.
      apply left_identity.
  Defined.
  Definition ConeMorphismRToL (cnC : Cone (graph_of G Gr)) (cnD : Cone Gr) :
    ConeMorphism cnC (cone_of G cnD) ->
    ConeMorphism (counitCone (cone_of F cnC)) cnD.
  Proof.
    intro mph. srapply mkCnMph.
    - simpl. refine (equiv_fun (equiv_hom_set_adjunction _ _ _) _).
      + apply adjunction_unit__of__adjunction_unit_counit. exact Adj.
      + apply (cnmph_mph mph).
    - intro n. simpl. rewrite <- (cnmph_comm mph).
      rewrite composition_of. repeat rewrite <- associativity. f_ap.
      simpl. rewrite (commutes (counit Adj)). reflexivity.
  Defined.
  Definition RightAdjunctLimit (L : Limit Gr) : Limit (graph_of G Gr).
  Proof.
    srapply mkLim; [ exact (cone_of G (lim_cone L)) | | ].
    - intro c. apply ConeMorphismLToR. apply lim_ex.
    - intros c m1 m2.
      pose (mph1 := ConeMorphismRToL m1). pose (mph2 := ConeMorphismRToL m2).
      refine (equiv_fun (equiv_ap'
                           (equiv_hom_set_adjunction
                              (adjunction_unit__of__adjunction_unit_counit Adj) _ _) _ _)^-1 _).
      exact (lim_uniq L _ mph1 mph2).
  Defined.

  Theorem RightAdjunctPreservesLimit : FunctorPreservesLimit G Gr.
  Proof.
    intro L. exists(RightAdjunctLimit L). reflexivity.
  Qed.
End AdjunctsPreserveLimits.
