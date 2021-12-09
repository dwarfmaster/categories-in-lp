
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.

Local Open Scope morphism_scope.

Definition fin1 : Fin 2 := inr tt.
Definition fin2 : Fin 2 := inl (inr tt).

Ltac empty_ind :=
  apply Empty_ind; assumption.
Ltac empty_ind' :=
  intro; empty_ind.

Record Graph {C : PreCategory} {size arrows : nat} :=
  mkGraph
    { gr_vertex : Fin size -> object C
    ; gr_edges : Fin arrows
               -> exists(src dst : Fin size), morphism C (gr_vertex src) (gr_vertex dst)
    }.
Arguments Graph C : clear implicits.

Definition gr_src {C : PreCategory} {s a : nat} (G : Graph C s a) (n : Fin a) : Fin s :=
  proj1 (gr_edges G n).
Definition gr_dst {C : PreCategory} {s a : nat} (G : Graph C s a) (n : Fin a) : Fin s :=
  proj1 (proj2 (gr_edges G n)).
Definition gr_src' {C : PreCategory} {s a : nat} (G : Graph C s a) (n : Fin a) : object C :=
  gr_vertex G (gr_src G n).
Definition gr_dst' {C : PreCategory} {s a : nat} (G : Graph C s a) (n : Fin a) : object C :=
  gr_vertex G (gr_dst G n).
Definition gr_edge {C : PreCategory} {s a : nat} (G : Graph C s a) (n : Fin a)
  : morphism C (gr_src' G n) (gr_dst' G n) :=
  proj2 (proj2 (gr_edges G n)).

Record Cone {C : PreCategory} {size arrows : nat} {G : Graph C size arrows} :=
  mkCone
    { cn_top  : object C
    ; cn_side : forall(n : Fin size), morphism C cn_top (gr_vertex G n)
    ; cn_comm : forall(a : Fin arrows), gr_edge G a o cn_side (gr_src G a) = cn_side (gr_dst G a)
    }.
Arguments Cone {C size arrows} G.
Record ConeMorphism {C : PreCategory} {size arrows : nat} {G : Graph C size arrows} {c1 c2 : Cone G} :=
  mkCnMph
    { cnmph_mph  : morphism C (cn_top c1) (cn_top c2)
    ; cnmph_comm : forall(n : Fin size), cn_side c2 n o cnmph_mph = cn_side c1 n
    }.
Arguments ConeMorphism {C size arrows G} c1 c2.
Record Limit {C : PreCategory} {size arrows : nat} {G : Graph C size arrows} :=
  mkLim
    { lim_cone : Cone G
    ; lim_ex   : forall(c : Cone G), ConeMorphism c lim_cone
    ; lim_uniq : forall(c : Cone G), forall(m1 m2 : ConeMorphism c lim_cone), cnmph_mph m1 = cnmph_mph m2
    }.
Arguments Limit {C size arrows} G.

Section GraphEqualizer.
  Context {C : PreCategory}.

  Definition EqualizerGr {a b : object C} (f g : morphism C a b) : Graph C 2 2.
  Proof.
    srapply mkGraph.
    - intro x. destruct x; [ exact b | exact a ].
    - intro x. destruct x.
      + exists fin1. exists fin2. exact f.
      + exists fin1. exists fin2. exact g.
  Defined.
  Definition Equalizer {a b : object C} (f g : morphism C a b) := Limit (EqualizerGr f g).
  Definition AllEqualizers := forall(a b : object C), forall(f g : morphism C a b), Equalizer f g.
  Definition eq_obj {a b : object C} (f g : morphism C a b) (E : Equalizer f g) : object C :=
    cn_top (lim_cone E).
  Definition eq_mph {a b : object C} (f g : morphism C a b) (E : Equalizer f g)
    : morphism C (eq_obj f g E) a :=
    cn_side (lim_cone E) fin1.
  Lemma eq_mph_comm {a b : object C} (f g : morphism C a b) (E : Equalizer f g) :
    f o eq_mph f g E = g o eq_mph f g E.
  Proof.
    unfold eq_mph. destruct E. simpl.
    pose (Hcomm := cn_comm (lim_cone0) fin1); unfold EqualizerGr in Hcomm;
      unfold gr_edge in Hcomm; unfold gr_src in Hcomm; unfold gr_dst in Hcomm;
      simpl in Hcomm.
    rewrite Hcomm; clear Hcomm.
    pose (Hcomm := cn_comm (lim_cone0) fin2); unfold EqualizerGr in Hcomm;
      unfold gr_edge in Hcomm; unfold gr_src in Hcomm; unfold gr_dst in Hcomm;
      simpl in Hcomm.
    rewrite Hcomm; clear Hcomm.
    reflexivity.
  Qed.

  Definition eq_cone {a b c : object C} (f g : morphism C a b) (h : morphism C c a) :
    f o h = g o h -> Cone (EqualizerGr f g).
  Proof.
    intro Hcomm. srapply mkCone.
    - exact c.
    - unfold EqualizerGr. simpl. intro n. destruct n; [ exact (f o h) | exact h ].
    - unfold EqualizerGr; unfold gr_edge; unfold gr_src; unfold gr_dst; simpl.
      intro n. destruct n; simpl; [ reflexivity | symmetry; exact Hcomm ].
  Defined.
  Lemma eq_ex {a b : object C} (f g : morphism C a b) (E : Equalizer f g) :
    forall(c : object C), forall(h : morphism C c a),
      f o h = g o h -> exists(e : morphism C c (eq_obj f g E)), h = eq_mph f g E o e.
  Proof.
    intros c h Hcomm. destruct E. unfold eq_mph. simpl.
    pose (cn := eq_cone f g h Hcomm). pose (mph := lim_ex0 cn).
    exists(cnmph_mph mph). rewrite (cnmph_comm mph fin1).
    unfold cn; unfold eq_cone; simpl. reflexivity.
  Qed.

  Definition eq_morphism {a b c1 : object C} (f g : morphism C a b)
             (h1 : morphism C c1 a) (H1 : f o h1 = g o h1) (E : Equalizer f g)
             (m : morphism C c1 (eq_obj f g E))
    : h1 = eq_mph f g E o m -> ConeMorphism (eq_cone f g h1 H1) (lim_cone E).
  Proof.
    intro Hcomm. srapply mkCnMph; [ exact m | idtac ].
    unfold EqualizerGr; intro n; destruct n; unfold eq_cone; simpl; simpl in *.
    - rewrite Hcomm. clear Hcomm. rewrite <- associativity. f_ap. unfold eq_mph; simpl.
      pose (Hcomm := cn_comm (lim_cone E) fin2);
        unfold gr_edge in Hcomm; unfold gr_src in Hcomm; unfold gr_dst in Hcomm;
        simpl in Hcomm. rewrite Hcomm. clear Hcomm.
      destruct f0; [ apply Empty_ind; assumption | destruct u; reflexivity ].
    - rewrite Hcomm. unfold eq_mph. destruct u. reflexivity.
  Defined.
  Lemma eq_uniq {a b c : object C} (f g : morphism C a b) (h : morphism C c a) (E : Equalizer f g) :
    forall(m1 m2 : morphism C c (eq_obj f g E)),
      f o h = g o h ->
      eq_mph f g E o m1 = h ->
      eq_mph f g E o m2 = h ->
      m1 = m2.
  Proof.
    intros m1 m2 Hcn Hm1 Hm2.
    pose (mph1 := eq_morphism f g h Hcn E m1 Hm1^).
    pose (mph2 := eq_morphism f g h Hcn E m2 Hm2^).
    destruct E; unfold eq_mph in *; unfold eq_obj in *; simpl in *.
    pose (uniq := lim_uniq0 (eq_cone f g h Hcn) mph1 mph2).
    unfold mph1 in uniq; unfold mph2 in uniq; simpl in uniq.
    exact uniq.
  Qed.
End GraphEqualizer.

Section GraphExtension.
  Context {C : PreCategory}.

  Definition ExtendArrow {size arrows : nat} (G : Graph C size arrows)
             (src dst : Fin size) (f : morphism C (gr_vertex G src) (gr_vertex G dst)) :
    Graph C size (S arrows).
  Proof.
    srapply mkGraph.
    - exact (gr_vertex G).
    - intro a. destruct a.
      + apply gr_edges. exact f0.
      + exact {| proj1 := src; proj2 := {| proj1 := dst; proj2 := f |} |}.
  Defined.
  Definition ExtendCone {size arrows : nat} {G : Graph C size arrows} (src dst : Fin size)
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

  Definition ExtendLimCone {size arrows : nat} (G : Graph C size arrows) (L : Limit G) :
    forall(src dst : Fin size),
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
    + intro vertex. exact (cn_side lim_cone0 vertex o tau).
    + intro arrow. simpl. rewrite <- associativity.
      destruct arrow; unfold ExtendArrow;
        unfold gr_src; unfold gr_dst; unfold gr_edge;
        simpl;
        (* On the first case, we remove tau because it commutes without it *)
        (* On the second case, the new arrows commutes from the property of the equalizer *)
        [ f_ap; clear tau | apply eq_mph_comm ].
      pose (Hcomm := cn_comm lim_cone0 f0);
        unfold gr_edge in Hcomm; unfold gr_src in Hcomm; unfold gr_dst in Hcomm;
        simpl in Hcomm.
      exact Hcomm.
  Defined.
  Lemma ExtendMorphism {size arrows : nat} (G : Graph C size arrows) (L : Limit G) :
    forall(src dst : Fin size),
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
  Lemma ExtendLimit (size arrows : nat) (G : Graph C size arrows) (L : Limit G) :
    forall(src dst : Fin size),
    forall(f : morphism C (gr_vertex G src) (gr_vertex G dst)),
    forall(E : Equalizer (f o cn_side (lim_cone L) src) (cn_side (lim_cone L) dst)),
      Limit (ExtendArrow G src dst f).
  Proof.
    intros src dst f E. pose (tau := eq_mph _ _ E). srapply mkLim.
    - exact (ExtendLimCone G L src dst f E).
    (* Showing the existence of a cone morphism from all cones *)
    - destruct L; simpl in *. intro c.
      (* We build a morphism from cn_top to the top of the previous limit *)
      pose (mph := lim_ex0 (ExtendCone src dst f c)).
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

End GraphExtension.

Section GraphDestruction.
  Context {C : PreCategory}.

  Definition RestrictArrow {size arrows : nat} (G : Graph C size (S arrows)) : Graph C size arrows
    := {| gr_vertex := gr_vertex G
       ;  gr_edges := fun a => gr_edges G (inl a)
       |}.
  Definition RestrictCone {size arrows : nat} {G : Graph C size (S arrows)} (c : Cone G) :
    Cone (RestrictArrow G).
  Proof.
    srapply mkCone.
    - exact (cn_top c).
    - exact (cn_side c).
    - intro a. apply (cn_comm c).
  Defined.
  Definition farr {size arrows : nat} (G : Graph C size (S arrows)) : Fin (S arrows) :=
    inr tt.

  Ltac graph_simpl H :=
    unfold ExtendArrow in H; unfold RestrictArrow in H; unfold farr in H;
    unfold gr_edge in H; unfold gr_src in H; unfold gr_dst in H;
    simpl in H.
  Ltac graph_simpl_goal :=
    unfold ExtendArrow; unfold RestrictArrow; unfold farr;
    unfold gr_edge; unfold gr_src; unfold gr_dst;
    simpl.

  Definition ConeExtendRestrict {size arrows : nat} (G : Graph C size (S arrows)) :
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
  Definition ConeRestrictExtend {size arrows : nat} (G : Graph C size (S arrows)) :
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
  Definition ConeExtendRestrictMorphism {size arrows : nat} (G : Graph C size (S arrows)) :
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
  Arguments ConeExtendRestrictMorphism {size arrows} G {c1 c2} m.
  Lemma LimitExtendRestrict (size arrows : nat) (G : Graph C size (S arrows)) :
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

End GraphDestruction.

Section GraphProduct.
  Context {C : PreCategory}.

  Definition ProductGr (a b : object C) : Graph C 2 0.
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

End GraphProduct.

Section GraphExtension.
  Context {C : PreCategory}.

  Definition ExtendVertices {size : nat} (G : Graph C size 0) (x : object C) : Graph C (S size) 0.
  Proof.
    srapply mkGraph; [ idtac | empty_ind' ].
    intro n. destruct n; [ idtac | exact x ].
    apply (gr_vertex G). exact f.
  Defined.

  Definition RestrictConeVert (size : nat) (G : Graph C size 0) (x : object C):
    forall(cn : Cone (ExtendVertices G x)), Cone G.
  Proof.
    intro cn. srapply mkCone; [ exact (cn_top cn) | idtac | empty_ind' ].
    intro n. exact (cn_side cn (inl n)).
  Defined.
  Definition ExtendConeVert (size : nat) (G : Graph C size 0) (x : object C):
    forall(cn : Cone G), forall(P : Product x (cn_top cn)),
      Cone (ExtendVertices G x).
  Proof.
    intros cn P. srapply mkCone.
    - exact (prod_obj P).
    - destruct n; [ idtac | exact (pi1 P) ].
      unfold ExtendVertices; simpl. apply (fun m => m o pi2 P). apply (cn_side cn).
    - empty_ind'.
  Defined.
  Definition RestrictConeVertMorphism (size : nat) (G : Graph C size 0) (x : object C):
    forall(c1 : Cone (ExtendVertices G x)), forall(c2 : Cone G),
    forall(P : Product x (cn_top c2)),
      ConeMorphism c1 (ExtendConeVert size G x c2 P) ->
      ConeMorphism (RestrictConeVert size G x c1) c2.
  Proof.
    intros c1 c2 P mph. srapply mkCnMph.
    - exact (pi2 P o cnmph_mph mph).
    - intro n. unfold RestrictConeVert; simpl. rewrite <- associativity.
      exact (cnmph_comm mph (inl n)).
  Defined.
  Lemma ExtendLimitVert (size : nat) (G : Graph C size 0) (x : object C):
    forall(L : Limit G), forall(P : Product x (cn_top (lim_cone L))),
      Limit (ExtendVertices G x).
  Proof.
    intros L P. srapply mkLim.
    - exact (ExtendConeVert size G x (lim_cone L) P).
    - intro c. pose (c' := RestrictConeVert size G x c). pose (mph := lim_ex L c').
      destruct (product_ex P (cn_top c) (cn_side c (inr tt)) (cnmph_mph mph))
               as [ m [ Hm1 Hm2 ] ].
      srapply mkCnMph; [ exact m
                       | intro v;
                         destruct v;
                         unfold ExtendConeVert; simpl;
                         [ idtac | symmetry; destruct u; exact Hm1 ] ].
      rewrite associativity. rewrite <- Hm2. exact (cnmph_comm mph f).
    - intros c m1 m2. apply (product_uniq P).
      + rewrite (cnmph_comm m1 (inr tt)). rewrite (cnmph_comm m2 (inr tt)). reflexivity.
      + pose (m1' := RestrictConeVertMorphism size G x c (lim_cone L) P m1).
        pose (m2' := RestrictConeVertMorphism size G x c (lim_cone L) P m2).
        exact (lim_uniq L _ m1' m2').
  Qed.

End GraphExtension.

Section GraphDestruction.
  Context {C : PreCategory}.

  Definition RestrictVertex {size : nat} (G : Graph C (S size) 0) : Graph C size 0.
  Proof.
    srapply mkGraph; [ idtac | empty_ind' ]. intro n.
    apply (gr_vertex G). exact (inl n).
  Defined.
  Definition fobj {size : nat} (G : Graph C (S size) 0) : object C :=
    gr_vertex G (inr tt).
  Definition RestrictExtendVertexCone {size : nat} (G : Graph C (S size) 0) :
    Cone G -> Cone (ExtendVertices (RestrictVertex G) (fobj G)).
  Proof.
    intro cn. srapply mkCone; [ exact (cn_top cn) | intro n | empty_ind' ].
    destruct n; apply (cn_side cn).
  Defined.

  Definition ConeRestrictExtendVertex {size : nat} (G : Graph C (S size) 0) :
    Cone (ExtendVertices (RestrictVertex G) (fobj G)) -> Cone G.
  Proof.
    intro cn. srapply mkCone; [ exact (cn_top cn) | idtac | empty_ind' ].
    intro n. destruct n; [ idtac | destruct u ].
    - apply (cn_side cn (inl f)).
    - apply (cn_side cn (inr tt)).
  Defined.
  Definition RestrictExtendVertexMorphism {size : nat} (G : Graph C (S size) 0) :
    forall(c1 : Cone G), forall(c2 : Cone (ExtendVertices (RestrictVertex G) (fobj G))),
      ConeMorphism c1 (ConeRestrictExtendVertex G c2) ->
      ConeMorphism (RestrictExtendVertexCone G c1) c2.
  Proof.
    intros c1 c2 mph. srapply mkCnMph; [ exact (cnmph_mph mph) | idtac ].
    intro n. destruct n; [ idtac | destruct u ]; simpl.
    - apply (cnmph_comm mph (inl f)).
    - apply (cnmph_comm mph (inr tt)).
  Defined.

  Lemma RestrictExtendLimitVert {size : nat} (G : Graph C (S size) 0) :
    Limit (ExtendVertices (RestrictVertex G) (fobj G)) -> Limit G.
  Proof.
    intro L. srapply mkLim.
    - exact (ConeRestrictExtendVertex G (lim_cone L)).
    - intro c. pose (c' := RestrictExtendVertexCone G c). pose (mph := lim_ex L c').
      srapply mkCnMph; [ exact (cnmph_mph mph) | idtac ].
      intro n. destruct n; [ idtac | destruct u ]; simpl.
      + apply (cnmph_comm mph (inl f)).
      + apply (cnmph_comm mph (inr tt)).
    - intros c m1 m2.
      pose (m1' := RestrictExtendVertexMorphism G _ _ m1).
      pose (m2' := RestrictExtendVertexMorphism G _ _ m2).
      exact (lim_uniq L _ m1' m2').
  Qed.

End GraphDestruction.

Section GraphTerminal.
  Context {C : PreCategory}.

  Definition TerminalGr : Graph C 0 0.
  Proof. srapply mkGraph; empty_ind'. Defined.
  Definition Terminal := Limit TerminalGr.
  Definition term_obj (T : Terminal) := cn_top (lim_cone T).

  Definition term_cone (c : object C) : Cone TerminalGr.
  Proof. srapply mkCone; [ exact c | empty_ind' | empty_ind' ]. Defined.
  Lemma terminal_ex (c : object C) (T : Terminal) : morphism C c (term_obj T).
  Proof. exact (cnmph_mph (lim_ex T (term_cone c))). Qed.

  Definition term_mph {c1 : object C} (c2 : Cone TerminalGr) (f : morphism C c1 (cn_top c2)) :
    ConeMorphism (term_cone c1) c2.
  Proof. srapply mkCnMph; [ exact f | empty_ind' ]. Defined.
  Lemma terminal_uniq (c : object C) (T : Terminal) :
    forall(f g : morphism C c (term_obj T)), f = g.
  Proof.
    intros f g. pose (f' := term_mph (lim_cone T) f). pose (g' := term_mph (lim_cone T) g).
    exact (lim_uniq T _ f' g').
  Qed.

End GraphTerminal.

Section GraphExtension.
  Context {C : PreCategory}.

  Lemma EmptyGraphLimit (G : Graph C 0 0):
    @Terminal C -> Limit G.
  Proof.
    intro T. srapply mkLim.
    - srapply mkCone; [ exact (term_obj T) | empty_ind' | empty_ind' ].
    - intro c. pose (mph := terminal_ex (cn_top c) T).
      srapply mkCnMph; [ exact mph | empty_ind' ].
    - intros c m1 m2. apply terminal_uniq.
  Qed.

End GraphExtension.

Theorem GraphLimitFromProductAndEqualizers (C : PreCategory)
        (T : @Terminal C) (P : @AllProducts C) (E : @AllEqualizers C) :
  forall(size arrows : nat), forall(G : Graph C size arrows), Limit G.
Proof.
  intros size arrows G. induction arrows; [ induction size | idtac ].
  - apply EmptyGraphLimit. exact T.
  - apply RestrictExtendLimitVert.
    apply (ExtendLimitVert size (RestrictVertex G) (fobj G) (IHsize (RestrictVertex G))).
    apply P.
  - apply LimitExtendRestrict.
    apply (ExtendLimit size arrows (RestrictArrow G) (IHarrows (RestrictArrow G))).
    apply E.
Qed.
