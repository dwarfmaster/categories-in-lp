
From HoTT Require Import Basics.
From HoTT Require Import Categories.
Require Import Finite.

Local Open Scope morphism_scope.

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
    - intro x. destruct x; [ exact a | exact b ].
    - intro x. destruct x.
      + exists (F1 2 1 1). exists (FS 2 1 1 (F1 1 0 1)). exact f.
      + exists (F1 2 1 1). exists (FS 2 1 1 (F1 1 0 1)). exact g.
  Defined.
  Definition Equalizer {a b : object C} (f g : morphism C a b) := Limit (EqualizerGr f g).
  Definition AllEqualizers := forall(a b : object C), forall(f g : morphism C a b), Equalizer f g.
  Definition eq_obj {a b : object C} (f g : morphism C a b) (E : Equalizer f g) : object C :=
    cn_top (lim_cone E).
  Definition eq_mph {a b : object C} (f g : morphism C a b) (E : Equalizer f g)
    : morphism C (eq_obj f g E) a :=
    cn_side (lim_cone E) (F1 2 1 1).
  Lemma eq_mph_comm {a b : object C} (f g : morphism C a b) (E : Equalizer f g) :
    f o eq_mph f g E = g o eq_mph f g E.
  Proof.
    unfold eq_mph. destruct E. simpl.
    pose (Hcomm := cn_comm (lim_cone0) (F1 2 1 1)); unfold EqualizerGr in Hcomm;
      unfold gr_edge in Hcomm; unfold gr_src in Hcomm; unfold gr_dst in Hcomm;
      simpl in Hcomm.
    rewrite Hcomm; clear Hcomm.
    pose (Hcomm := cn_comm (lim_cone0) (FS 2 1 1 (F1 1 0 1))); unfold EqualizerGr in Hcomm;
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
    - unfold EqualizerGr. simpl. intro n. destruct n; [ exact h | exact (f o h) ].
    - unfold EqualizerGr; unfold gr_edge; unfold gr_src; unfold gr_dst; simpl.
      intro n. destruct n; simpl; [ reflexivity | symmetry; exact Hcomm ].
  Defined.
  Lemma eq_ex {a b : object C} (f g : morphism C a b) (E : Equalizer f g) :
    forall(c : object C), forall(h : morphism C c a),
      f o h = g o h -> exists(e : morphism C c (eq_obj f g E)), h = eq_mph f g E o e.
  Proof.
    intros c h Hcomm. destruct E. unfold eq_mph. simpl.
    pose (cn := eq_cone f g h Hcomm). pose (mph := lim_ex0 cn).
    exists(cnmph_mph mph). rewrite (cnmph_comm mph (F1 2 1 1)).
    unfold cn; unfold eq_cone; simpl. reflexivity.
  Qed.

  Definition eq_morphism {a b c1 : object C} (f g : morphism C a b)
             (h1 : morphism C c1 a) (H1 : f o h1 = g o h1) (E : Equalizer f g)
             (m : morphism C c1 (eq_obj f g E))
    : h1 = eq_mph f g E o m -> ConeMorphism (eq_cone f g h1 H1) (lim_cone E).
  Proof.
    intro Hcomm. srapply mkCnMph; [ exact m | idtac ].
    unfold EqualizerGr; intro n; destruct (fin_destr _ n) as [ Hn | [ n' Hn ] ]; rewrite Hn;
      unfold eq_cone; simpl; simpl in *.
    - rewrite Hcomm. unfold eq_mph. reflexivity.
    - rewrite Hcomm. clear Hcomm. rewrite <- associativity. f_ap. unfold eq_mph; simpl.
      pose (Hcomm := cn_comm (lim_cone E) (F1 2 1 1));
        unfold gr_edge in Hcomm; unfold gr_src in Hcomm; unfold gr_dst in Hcomm;
        simpl in Hcomm. rewrite Hcomm.
      destruct (fin_destr _ n') as [ Hn' | [ n'' Hn' ] ]; rewrite Hn';
        [ reflexivity | inv_fin_0 ].
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
      + exact {| proj1 := src; proj2 := {| proj1 := dst; proj2 := f |} |}.
      + apply gr_edges. apply Nat.path_nat_S in p. rewrite p. exact a.
  Defined.
  Definition ExtendCone {size arrows : nat} {G : Graph C size arrows} (src dst : Fin size)
    (f : morphism C (gr_vertex G src) (gr_vertex G dst))
    (c : Cone (ExtendArrow G src dst f)) : Cone G.
  Proof.
    srapply mkCone.
    - exact (cn_top c).
    - exact (cn_side c).
    - intro a. pose (na := FS _ _ 1 a).
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
        (* On the first case, the new arrows commutes from the property of the equalizer *)
        (* On the second case, we remove tau because it commutes without it *)
        [ apply eq_mph_comm | f_ap; clear tau ].
      pose (inj_arrow := internal_paths_rew_r nat arrows m
             (fun n : nat => Fin n) arrow (Nat.path_nat_S arrows m p)).
      assert (inj_arrow = internal_paths_rew_r nat arrows m
                            (fun n : nat => Fin n) arrow (Nat.path_nat_S arrows m p))
             as Heq by reflexivity.
      rewrite <- Heq. clear Heq.
      pose (Hcomm := cn_comm lim_cone0 inj_arrow);
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
        apply (cn_comm c (F1 _ arrows 1)). }
      srapply mkCnMph; simpl; [ exact (mphE.1) | intro n ].
      unfold tau. rewrite associativity. rewrite <- mphE.2.
      apply (cnmph_comm mph n).
    (* Showing the unicity of a cone morphism from all cones *)
    - intros c m1 m2. apply (eq_uniq _ _ (tau o cnmph_mph m1) E); try reflexivity.
      + rewrite <- associativity. rewrite <- associativity. f_ap.
        unfold tau. unfold eq_mph.
        pose (Hcomm := cn_comm (lim_cone E) (F1 2 1 1));
          unfold gr_edge in Hcomm; unfold gr_src in Hcomm; unfold gr_dst in Hcomm;
          simpl in Hcomm.
        rewrite Hcomm. clear Hcomm.
        pose (Hcomm := cn_comm (lim_cone E) (FS 2 1 1 (F1 1 0 1)));
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
       ;  gr_edges := fun a => gr_edges G (FS _ arrows 1 a)
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
    F1 _ arrows 1.

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
      destruct (fin_destr _ a) as [ Ha | [ a' Ha ] ];
        rewrite Ha in Hcomm; simpl in Hcomm;
        graph_simpl_goal; rewrite Ha; exact Hcomm.
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
      destruct (fin_destr _ a) as [ Ha | [ a' Ha ] ];
        rewrite Ha in Hcomm; simpl in Hcomm;
        graph_simpl_goal; rewrite Ha; exact Hcomm.
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
    - destruct x; [ exact a | exact b ].
    - inv_fin_0.
  Defined.
  Definition Product (a b : object C) := Limit (ProductGr a b).
  Definition prod_obj {a b : object C} (p : Product a b) : object C :=
    cn_top (lim_cone p).
  Definition pi1 {a b : object C} (p : Product a b) : morphism C (prod_obj p) a :=
    cn_side (lim_cone p) (F1 2 1 1).
  Definition pi2 {a b : object C} (p : Product a b) : morphism C (prod_obj p) b :=
    cn_side (lim_cone p) (FS 2 1 1 (F1 1 0 1)).

  Definition prod_cone {a b c : object C} (f : morphism C c a) (g : morphism C c b) :
    Cone (ProductGr a b).
  Proof.
    srapply mkCone.
    - exact c.
    - intro n; destruct n; [ exact f | exact g ].
    - inv_fin_0'.
  Defined.
  Lemma product_ex {a b : object C} (P : Product a b) :
    forall(c : object C), forall(f : morphism C c a), forall(g : morphism C c b),
      exists(e : morphism C c (prod_obj P)), f = pi1 P o e /\ g = pi2 P o e.
  Proof.
    intros c f g. pose (cn := prod_cone f g). pose (mph := lim_ex P cn). exists(cnmph_mph mph).
    split; [ pose (Hcomm := cnmph_comm mph (F1 2 1 1))
           | pose (Hcomm := cnmph_comm mph (FS 2 1 1 (F1 1 0 1))) ];
      symmetry; exact Hcomm.
  Qed.

  Definition prod_mph {a b c : object C} (f : morphism C c a) (g : morphism C c b) :
    forall(cn : Cone (ProductGr a b)), forall(m : morphism C c (cn_top cn)),
      cn_side cn (F1 2 1 1) o m = f ->
      cn_side cn (FS 2 1 1 (F1 1 0 1)) o m = g ->
      ConeMorphism (prod_cone f g) cn.
  Proof.
    intros cn m H1 H2. srapply mkCnMph; [ exact m | idtac ].
    intro n; destruct (fin_destr _ n) as [ Hn | [ n' Hn ] ]; rewrite Hn.
    - rewrite H1. reflexivity.
    - destruct (fin_destr _ n') as [ Hn' | [ n'' _ ] ].
      + rewrite Hn'. rewrite H2. reflexivity.
      + inv_fin_0.
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
    srapply mkGraph.
    - intro n. destruct n; [ exact x | idtac ].
      apply (gr_vertex G). apply Nat.path_nat_S in p. rewrite p. exact n.
    - inv_fin_0'.
  Defined.

  Definition RestrictConeVert (size : nat) (G : Graph C size 0) (x : object C):
    forall(cn : Cone (ExtendVertices G x)), Cone G.
  Proof.
    intro cn. srapply mkCone.
    - exact (cn_top cn).
    - intro n. exact (cn_side cn (FS _ size 1 n)).
    - inv_fin_0'.
  Defined.
  Definition ExtendConeVert (size : nat) (G : Graph C size 0) (x : object C):
    forall(cn : Cone G), forall(P : Product x (cn_top cn)),
      Cone (ExtendVertices G x).
  Proof.
    intros cn P. srapply mkCone.
    - exact (prod_obj P).
    - destruct n; [ exact (pi1 P) | idtac ].
      unfold ExtendVertices; simpl. apply (fun m => m o pi2 P). apply (cn_side cn).
    - inv_fin_0'.
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
      exact (cnmph_comm mph (FS _ size 1 n)).
  Defined.
  Lemma ExtendLimitVert (size : nat) (G : Graph C size 0) (x : object C):
    forall(L : Limit G), forall(P : Product x (cn_top (lim_cone L))),
      Limit (ExtendVertices G x).
  Proof.
    intros L P. srapply mkLim.
    - exact (ExtendConeVert size G x (lim_cone L) P).
    - intro c. pose (c' := RestrictConeVert size G x c). pose (mph := lim_ex L c').
      destruct (product_ex P (cn_top c) (cn_side c (F1 _ size 1)) (cnmph_mph mph))
               as [ m [ Hm1 Hm2 ] ].
      srapply mkCnMph; [ exact m
                       | intro v;
                         destruct (fin_destr _ v) as [ Hv | [ v' Hv ] ];
                         rewrite Hv;
                         unfold ExtendConeVert; simpl;
                         [ symmetry; exact Hm1 | idtac ] ].
      rewrite associativity. rewrite <- Hm2. exact (cnmph_comm mph v').
    - intros c m1 m2. apply (product_uniq P).
      + rewrite (cnmph_comm m1 (F1 _ size 1)). rewrite (cnmph_comm m2 (F1 _ size 1)). reflexivity.
      + pose (m1' := RestrictConeVertMorphism size G x c (lim_cone L) P m1).
        pose (m2' := RestrictConeVertMorphism size G x c (lim_cone L) P m2).
        exact (lim_uniq L _ m1' m2').
  Qed.

End GraphExtension.

