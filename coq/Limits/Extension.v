
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
Require Import Misc.
Require Import Limits.Graph.
Require Import Limits.Equalizer.
Require Import Limits.Product.
Require Import Limits.Terminal.

Local Open Scope morphism_scope.

Section GraphExtension.
  Context {C : PreCategory}.

  Definition ExtendArrow {Size Arrows : Type} (G : Graph C Size Arrows)
             (src dst : Size) (f : morphism C (gr_vertex G src) (gr_vertex G dst)) :
    Graph C Size (Arrows + Unit).
  Proof.
    srapply mkGraph.
    - exact (gr_vertex G).
    - intro a. destruct a.
      + apply gr_edges. exact a.
      + exact {| proj1 := src; proj2 := {| proj1 := dst; proj2 := f |} |}.
  Defined.
  Definition ExtendCone {Size Arrows : Type} {G : Graph C Size Arrows} (src dst : Size)
    (f : morphism C (gr_vertex G src) (gr_vertex G dst))
    (c : Cone (ExtendArrow G src dst f)) : Cone G.
  Proof.
    srapply mkCone.
    - exact (cn_top c).
    - exact (cn_side c).
    - intro a. pose (na := @inl _ Unit a).
      pose (Hcomm := cn_comm c na); unfold ExtendArrow in Hcomm;
        unfold gr_edge in Hcomm; unfold gr_src in Hcomm; unfold gr_dst in Hcomm;
        simpl in Hcomm.
      unfold gr_edge; unfold gr_src; unfold gr_dst; simpl.
      exact Hcomm.
  Defined.

  Definition ExtendLimCone {Size Arrows : Type} (G : Graph C Size Arrows) (L : Limit G) :
    forall(src dst : Size),
    forall(f : morphism C (gr_vertex G src) (gr_vertex G dst)),
    forall(E : Equalizer (f o cn_side (lim_cone L) src) (cn_side (lim_cone L) dst)),
      Cone (ExtendArrow G src dst f).
  Proof.
    intros src dst f E. destruct L; simpl in *.
    pose (tau := eq_mph _ _ E).
    srapply mkCone.
    (* The top is the top of the equalizer *)
    + exact (eq_obj _ _ E).
    (* The edges are the edges of the previous limit composed with the equalizer *)
    + intro vertex. exact (cn_side lim_cone vertex o tau).
    + intro arrow. simpl. rewrite <- associativity.
      destruct arrow; unfold ExtendArrow;
        unfold gr_src; unfold gr_dst; unfold gr_edge;
        simpl;
        (* On the first case, we remove tau because it commutes without it *)
        (* On the second case, the new arrows commutes from the property of the equalizer *)
        [ f_ap; clear tau | apply eq_mph_comm ].
      pose (Hcomm := cn_comm lim_cone a);
        unfold gr_edge in Hcomm; unfold gr_src in Hcomm; unfold gr_dst in Hcomm;
        simpl in Hcomm.
      exact Hcomm.
  Defined.
  Lemma ExtendMorphism {Size Arrows : Type} (G : Graph C Size Arrows) (L : Limit G) :
    forall(src dst : Size),
    forall(f : morphism C (gr_vertex G src) (gr_vertex G dst)),
    forall(E : Equalizer (f o cn_side (lim_cone L) src) (cn_side (lim_cone L) dst)),
    forall(c : Cone (ExtendArrow G src dst f)),
    forall(m : ConeMorphism c (ExtendLimCone G L src dst f E)),
    exists(m' : ConeMorphism (ExtendCone src dst f c) (lim_cone L)),
      cnmph_mph m' = eq_mph _ _ E o cnmph_mph m.
  Proof.
    intros src dst f E c m. simple refine {| proj1 := _; proj2 := _ |}.
    - srapply mkCnMph; [ exact (eq_mph _ _ E o cnmph_mph m) | idtac ].
      intro n. unfold ExtendCone; simpl.
      rewrite <- associativity. apply (cnmph_comm m n).
    - reflexivity.
  Qed.
  Lemma ExtendLimit (Size Arrows : Type) (G : Graph C Size Arrows) (L : Limit G) :
    forall(src dst : Size),
    forall(f : morphism C (gr_vertex G src) (gr_vertex G dst)),
    forall(E : Equalizer (f o cn_side (lim_cone L) src) (cn_side (lim_cone L) dst)),
      Limit (ExtendArrow G src dst f).
  Proof.
    intros src dst f E. pose (tau := eq_mph _ _ E). srapply mkLim.
    - exact (ExtendLimCone G L src dst f E).
    (* Showing the existence of a cone morphism from all cones *)
    - destruct L; simpl in *. intro c.
      (* We build a morphism from cn_top to the top of the previous limit *)
      pose (mph := lim_ex (ExtendCone src dst f c)).
      (* We show that to get a morphism to the equalizer, it is enough that the previous
         morphism commutes with the two arrows *)
      assert (exists(e : morphism C (cn_top c) (eq_obj _ _ E)), cnmph_mph mph = eq_mph _ _ E o e) as mphE.
      { refine (eq_ex _ _ E (cn_top c) (cnmph_mph mph) _).
        (* We show that it is the case since it comes from a cone on the extended graph *)
        rewrite associativity. rewrite (cnmph_comm mph src). rewrite (cnmph_comm mph dst).
        unfold ExtendCone; simpl.
        apply (cn_comm c (inr tt)). }
      srapply mkCnMph; simpl; [ exact (mphE.1) | intro n ].
      unfold tau. rewrite associativity. rewrite <- mphE.2.
      apply (cnmph_comm mph n).
    (* Showing the unicity of a cone morphism from all cones *)
    - intros c m1 m2. apply (eq_uniq _ _ (tau o cnmph_mph m1) E); try reflexivity.
      + rewrite <- associativity. rewrite <- associativity. f_ap.
        unfold tau. unfold eq_mph.
        pose (Hcomm := cn_comm (lim_cone E) fin1);
          unfold gr_edge in Hcomm; unfold gr_src in Hcomm; unfold gr_dst in Hcomm;
          simpl in Hcomm.
        rewrite Hcomm. clear Hcomm.
        pose (Hcomm := cn_comm (lim_cone E) fin2);
          unfold gr_edge in Hcomm; unfold gr_src in Hcomm; unfold gr_dst in Hcomm;
          simpl in Hcomm.
        rewrite Hcomm. clear Hcomm.
        reflexivity.
      + destruct (ExtendMorphism G L src dst f E c m1) as [ m1' H1 ].
        rewrite <- H1. clear H1.
        destruct (ExtendMorphism G L src dst f E c m2) as [ m2' H2 ].
        rewrite <- H2. clear H2.
        apply (lim_uniq L _ m2' m1').
  Qed.

  Definition RestrictArrow {Size Arrows : Type} (G : Graph C Size (Arrows + Unit)) : Graph C Size Arrows
    := {| gr_vertex := gr_vertex G
       ;  gr_edges := fun a => gr_edges G (inl a)
       |}.
  Definition RestrictCone {Size Arrows : Type} {G : Graph C Size (Arrows + Unit)} (c : Cone G) :
    Cone (RestrictArrow G).
  Proof.
    srapply mkCone.
    - exact (cn_top c).
    - exact (cn_side c).
    - intro a. apply (cn_comm c).
  Defined.
  Definition farr {Size Arrows : Type} (G : Graph C Size (Arrows + Unit)) : Arrows + Unit :=
    inr tt.

  Ltac graph_simpl H :=
    unfold ExtendArrow in H; unfold RestrictArrow in H; unfold farr in H;
    unfold gr_edge in H; unfold gr_src in H; unfold gr_dst in H;
    simpl in H.
  Ltac graph_simpl_goal :=
    unfold ExtendArrow; unfold RestrictArrow; unfold farr;
    unfold gr_edge; unfold gr_src; unfold gr_dst;
    simpl.

  Definition ConeExtendRestrict {Size Arrows : Type} (G : Graph C Size (Arrows + Unit)) :
    forall(cn : Cone (ExtendArrow (RestrictArrow G)
                             (gr_src G (farr G))
                             (gr_dst G (farr G))
                             (gr_edge G (farr G)))),
      Cone G.
  Proof.
    simpl. intro cn. srapply mkCone.
    - exact (cn_top cn).
    - exact (cn_side cn).
    - intro a. pose (Hcomm := cn_comm cn a); graph_simpl Hcomm.
      destruct a; try (destruct u); exact Hcomm.
  Defined.
  Definition ConeRestrictExtend {Size Arrows : Type} (G : Graph C Size (Arrows + Unit)) :
    forall(cn : Cone G),
      Cone (ExtendArrow (RestrictArrow G)
                        (gr_src G (farr G))
                        (gr_dst G (farr G))
                        (gr_edge G (farr G))).
  Proof.
    intro cn. srapply mkCone.
    - exact (cn_top cn).
    - exact (cn_side cn).
    - intro a. pose (Hcomm := cn_comm cn a); graph_simpl Hcomm.
      destruct a; try (destruct u); exact Hcomm.
  Defined.
  Definition ConeExtendRestrictMorphism {Size Arrows : Type} (G : Graph C Size (Arrows + Unit)) :
    let G' := ExtendArrow (RestrictArrow G)
                          (gr_src G (farr G))
                          (gr_dst G (farr G))
                          (gr_edge G (farr G)) in
    forall(c1 : Cone G), forall(c2 : Cone G'), forall(m : ConeMorphism c1 (ConeExtendRestrict G c2)),
      ConeMorphism (ConeRestrictExtend G c1) c2.
  Proof.
    simpl. intros c1 c2 mph. srapply mkCnMph.
    - exact (cnmph_mph mph).
    - intro n. apply (cnmph_comm mph).
  Defined.
  Arguments ConeExtendRestrictMorphism {Size Arrows} G {c1 c2} m.
  Lemma LimitExtendRestrict (Size Arrows : Type) (G : Graph C Size (Arrows + Unit)) :
    forall(L : Limit (ExtendArrow (RestrictArrow G)
                             (gr_src G (farr G))
                             (gr_dst G (farr G))
                             (gr_edge G (farr G)))),
      Limit G.
  Proof.
    simpl. intro L. srapply mkLim.
    - exact (ConeExtendRestrict G (lim_cone L)).
    - intro c. pose (c' := ConeRestrictExtend G c). pose (mph := lim_ex L c').
      srapply mkCnMph.
      + exact (cnmph_mph mph).
      + intro n. unfold ConeExtendRestrict; simpl. apply (cnmph_comm mph).
    - intro c. pose (c' := ConeRestrictExtend G c). intros m1 m2.
      pose (m1' := ConeExtendRestrictMorphism G m1).
      pose (m2' := ConeExtendRestrictMorphism G m2).
      apply (lim_uniq L _ m1' m2').
  Qed.

  Definition ExtendVertices {Size Arrows : Type} (G : Graph C Size Arrows) (x : object C) :
    Graph C (Size + Unit) Arrows.
  Proof.
    srapply mkGraph.
    - intro n. destruct n; [ idtac | exact x ].
      apply (gr_vertex G). exact s.
    - intro a. destruct (gr_edges G a) as [ src [ dst f ] ].
      exists(inl src). exists(inl dst). exact f.
  Defined.

  Definition RestrictConeVert {Size Arrows : Type} (G : Graph C Size Arrows) (x : object C):
    forall(cn : Cone (ExtendVertices G x)), Cone G.
  Proof.
    intro cn. srapply mkCone; [ exact (cn_top cn) | idtac | idtac ].
    - intro n. exact (cn_side cn (inl n)).
    - intro a. simpl. apply (cn_comm cn a).
  Defined.
  Definition ExtendConeVert {Size Arrows : Type} (G : Graph C Size Arrows) (x : object C):
    forall(cn : Cone G), forall(P : Product x (cn_top cn)),
      Cone (ExtendVertices G x).
  Proof.
    intros cn P. srapply mkCone.
    - exact (prod_obj P).
    - destruct n; [ idtac | exact (pi1 P) ].
      unfold ExtendVertices; simpl. apply (fun m => m o pi2 P). apply (cn_side cn).
    - intro a. simpl. rewrite <- associativity. f_ap. apply (cn_comm cn).
  Defined.
  Definition RestrictConeVertMorphism {Size Arrows : Type} (G : Graph C Size Arrows) (x : object C):
    forall(c1 : Cone (ExtendVertices G x)), forall(c2 : Cone G),
    forall(P : Product x (cn_top c2)),
      ConeMorphism c1 (ExtendConeVert G x c2 P) ->
      ConeMorphism (RestrictConeVert G x c1) c2.
  Proof.
    intros c1 c2 P mph. srapply mkCnMph.
    - exact (pi2 P o cnmph_mph mph).
    - intro n. unfold RestrictConeVert; simpl. rewrite <- associativity.
      exact (cnmph_comm mph (inl n)).
  Defined.
  Lemma ExtendLimitVert {Size Arrows : Type} (G : Graph C Size Arrows) (x : object C):
    forall(L : Limit G), forall(P : Product x (cn_top (lim_cone L))),
      Limit (ExtendVertices G x).
  Proof.
    intros L P. srapply mkLim.
    - exact (ExtendConeVert G x (lim_cone L) P).
    - intro c. pose (c' := RestrictConeVert G x c). pose (mph := lim_ex L c').
      destruct (product_ex P (cn_top c) (cn_side c (inr tt)) (cnmph_mph mph))
               as [ m [ Hm1 Hm2 ] ].
      srapply mkCnMph; [ exact m
                       | intro v;
                         destruct v;
                         unfold ExtendConeVert; simpl;
                         [ idtac | symmetry; destruct u; exact Hm1 ] ].
      rewrite associativity. rewrite <- Hm2. exact (cnmph_comm mph s).
    - intros c m1 m2. apply (product_uniq P).
      + rewrite (cnmph_comm m1 (inr tt)). rewrite (cnmph_comm m2 (inr tt)). reflexivity.
      + pose (m1' := RestrictConeVertMorphism G x c (lim_cone L) P m1).
        pose (m2' := RestrictConeVertMorphism G x c (lim_cone L) P m2).
        exact (lim_uniq L _ m1' m2').
  Qed.

  Definition RestrictVertex {Size : Type} (G : Graph C (Size + Unit) Empty) : Graph C Size Empty.
  Proof.
    srapply mkGraph; [ idtac | empty_ind' ]. intro n.
    apply (gr_vertex G). exact (inl n).
  Defined.
  Definition fobj {Size : Type} (G : Graph C (Size + Unit) Empty) : object C :=
    gr_vertex G (inr tt).
  Definition RestrictExtendVertexCone {Size : Type} (G : Graph C (Size + Unit) Empty) :
    Cone G -> Cone (ExtendVertices (RestrictVertex G) (fobj G)).
  Proof.
    intro cn. srapply mkCone; [ exact (cn_top cn) | intro n | empty_ind' ].
    destruct n; apply (cn_side cn).
  Defined.

  Definition ConeRestrictExtendVertex {Size : Type} (G : Graph C (Size + Unit) Empty) :
    Cone (ExtendVertices (RestrictVertex G) (fobj G)) -> Cone G.
  Proof.
    intro cn. srapply mkCone; [ exact (cn_top cn) | idtac | empty_ind' ].
    intro n. destruct n; [ idtac | destruct u ].
    - apply (cn_side cn (inl s)).
    - apply (cn_side cn (inr tt)).
  Defined.
  Definition RestrictExtendVertexMorphism {Size : Type} (G : Graph C (Size + Unit) Empty) :
    forall(c1 : Cone G), forall(c2 : Cone (ExtendVertices (RestrictVertex G) (fobj G))),
      ConeMorphism c1 (ConeRestrictExtendVertex G c2) ->
      ConeMorphism (RestrictExtendVertexCone G c1) c2.
  Proof.
    intros c1 c2 mph. srapply mkCnMph; [ exact (cnmph_mph mph) | idtac ].
    intro n. destruct n; [ idtac | destruct u ]; simpl.
    - apply (cnmph_comm mph (inl s)).
    - apply (cnmph_comm mph (inr tt)).
  Defined.

  Lemma RestrictExtendLimitVert {Size : Type} (G : Graph C (Size + Unit) Empty) :
    Limit (ExtendVertices (RestrictVertex G) (fobj G)) -> Limit G.
  Proof.
    intro L. srapply mkLim.
    - exact (ConeRestrictExtendVertex G (lim_cone L)).
    - intro c. pose (c' := RestrictExtendVertexCone G c). pose (mph := lim_ex L c').
      srapply mkCnMph; [ exact (cnmph_mph mph) | idtac ].
      intro n. destruct n; [ idtac | destruct u ]; simpl.
      + apply (cnmph_comm mph (inl s)).
      + apply (cnmph_comm mph (inr tt)).
    - intros c m1 m2.
      pose (m1' := RestrictExtendVertexMorphism G _ _ m1).
      pose (m2' := RestrictExtendVertexMorphism G _ _ m2).
      exact (lim_uniq L _ m1' m2').
  Qed.

End GraphExtension.

Theorem AllEmptyFromTerminal (C : PreCategory) (G : Graph C Empty Empty):
  Terminal C -> Limit G.
Proof.
  intro T. srapply mkLim.
  - srapply mkCone; [ exact (term_obj T) | empty_ind' | empty_ind' ].
  - intro c. pose (mph := terminal_ex (cn_top c) T).
    srapply mkCnMph; [ exact mph | empty_ind' ].
  - intros c m1 m2. apply terminal_uniq.
Qed.

Theorem AllProductsFromProduct (C : PreCategory)
        (T : @Terminal C) (P : @AllProducts C) :
  forall(size : nat), forall(G : Graph C (Fin size) Empty), Limit G.
Proof.
  intros size G. induction size.
  - apply AllEmptyFromTerminal. exact T.
  - apply RestrictExtendLimitVert.
    apply (ExtendLimitVert (RestrictVertex G) (fobj G) (IHsize (RestrictVertex G))).
    apply P.
Qed.

Theorem AllLimitsFromProductAndEqualizer (C : PreCategory)
        (T : @Terminal C) (P : @AllProducts C) (E : @AllEqualizers C) :
  HasFiniteLimits C.
Proof.
  intros size arrows G. induction arrows; [ apply AllProductsFromProduct; assumption | idtac ].
  apply LimitExtendRestrict.
  apply (ExtendLimit _ _ (RestrictArrow G) (IHarrows (RestrictArrow G))).
  apply E.
Qed.

