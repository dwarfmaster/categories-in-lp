
From HoTT Require Import Basics.
From HoTT Require Import Categories.
Require Import Finite.

Local Open Scope morphism_scope.

Record Graph {C : PreCategory} :=
  mkGraph
    { gr_size : nat
    ; gr_vertex : Fin gr_size -> object C
    ; gr_nb_arrows : nat
    ; gr_edges : Fin gr_nb_arrows
               -> exists(src dst : Fin gr_size), morphism C (gr_vertex src) (gr_vertex dst)
    }.
Arguments Graph C : clear implicits.

Definition gr_src {C : PreCategory} (G : Graph C) (n : Fin (gr_nb_arrows G)) : Fin (gr_size G) :=
  proj1 (gr_edges G n).
Definition gr_dst {C : PreCategory} (G : Graph C) (n : Fin (gr_nb_arrows G)) : Fin (gr_size G) :=
  proj1 (proj2 (gr_edges G n)).
Definition gr_src' {C : PreCategory} (G : Graph C) (n : Fin (gr_nb_arrows G)) : object C :=
  gr_vertex G (gr_src G n).
Definition gr_dst' {C : PreCategory} (G : Graph C) (n : Fin (gr_nb_arrows G)) : object C :=
  gr_vertex G (gr_dst G n).
Definition gr_edge {C : PreCategory} (G : Graph C) (n : Fin (gr_nb_arrows G))
  : morphism C (gr_src' G n) (gr_dst' G n) :=
  proj2 (proj2 (gr_edges G n)).

Record Cone {C : PreCategory} {G : Graph C} :=
  mkCone
    { cn_top  : object C
    ; cn_side : forall(n : Fin (gr_size G)), morphism C cn_top (gr_vertex G n)
    ; cn_comm : forall(a : Fin (gr_nb_arrows G)), gr_edge G a o cn_side (gr_src G a) = cn_side (gr_dst G a)
    }.
Arguments Cone {C} G.
Record ConeMorphism {C : PreCategory} {G : Graph C} {c1 c2 : Cone G} :=
  mkCnMph
    { cnmph_mph  : morphism C (cn_top c1) (cn_top c2)
    ; cnmph_comm : forall(n : Fin (gr_size G)), cn_side c2 n o cnmph_mph = cn_side c1 n
    }.
Arguments ConeMorphism {C G} c1 c2.
Record Limit {C : PreCategory} {G : Graph C} :=
  mkLim
    { lim_cone : Cone G
    ; lim_ex   : forall(c : Cone G), ConeMorphism c lim_cone
    ; lim_uniq : forall(c : Cone G), forall(m1 m2 : ConeMorphism c lim_cone), cnmph_mph m1 = cnmph_mph m2
    }.
Arguments Limit {C} G.

Section GraphEqualizer.
  Context {C : PreCategory}.

  Definition EqualizerGr {a b : object C} (f g : morphism C a b) : Graph C.
  Proof.
    srapply mkGraph.
    - exact 2%nat.
    - intro x. destruct x; [ exact a | exact b ].
    - exact 2%nat.
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
        destruct (fin_destr _ n') as [ Hn' | [ n'' Hn' ] ]; rewrite Hn'; try reflexivity.
      apply Empty_ind. apply fin_0. exact n''.
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

Section GraphLemmas.
  Context {C : PreCategory}.

  Definition RestrictArrow (G : Graph C) : Graph C :=
    {| gr_size := gr_size G
    ;  gr_vertex := gr_vertex G
    ;  gr_nb_arrows := pred (gr_nb_arrows G)
    ;  gr_edges := fun n => gr_edges G (inj_pred n)
    |}.
  Definition RestrictCone {G : Graph C} (c : Cone G) : Cone (RestrictArrow G).
  Proof.
    srapply mkCone.
    - exact (cn_top c).
    - exact (cn_side c).
    - unfold gr_edge. unfold gr_src. unfold gr_dst. unfold RestrictArrow. simpl.
      intro a. apply (cn_comm c).
  Defined.

  Definition ExtendArrow (G : Graph C) (src dst : Fin (gr_size G))
             (f : morphism C (gr_vertex G src) (gr_vertex G dst)) : Graph C.
  Proof.
    srapply mkGraph.
    - exact (gr_size G).
    - exact (gr_vertex G).
    - exact (S (gr_nb_arrows G)).
    - intro a. destruct a.
      + exact {| proj1 := src; proj2 := {| proj1 := dst; proj2 := f |} |}.
      + apply gr_edges. apply Nat.path_nat_S in p. rewrite p. exact a.
  Defined.
  Definition ExtendCone {G : Graph C} (src dst : Fin (gr_size G))
    (f : morphism C (gr_vertex G src) (gr_vertex G dst))
    (c : Cone (ExtendArrow G src dst f)) : Cone G.
  Proof.
    srapply mkCone.
    - exact (cn_top c).
    - exact (cn_side c).
    - intro a. pose (na := FS _ _ 1 a).
      assert ((S (gr_nb_arrows G)) = gr_nb_arrows (ExtendArrow G src dst f)) as Harrs.
      { unfold ExtendArrow. reflexivity. }
      pose (Hcomm := cn_comm c na); unfold ExtendArrow in Hcomm;
        unfold gr_edge in Hcomm; unfold gr_src in Hcomm; unfold gr_dst in Hcomm;
        simpl in Hcomm.
      unfold gr_edge; unfold gr_src; unfold gr_dst; simpl.
      exact Hcomm.
  Defined.

  Definition ExtendLimCone (G : Graph C) (L : Limit G) :
    forall(src dst : Fin (gr_size G)),
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
      pose (inj_arrow := internal_paths_rew_r nat (gr_nb_arrows G) m
             (fun n : nat => Fin n) arrow (Nat.path_nat_S (gr_nb_arrows G) m p)).
      assert (inj_arrow = internal_paths_rew_r nat (gr_nb_arrows G) m
                            (fun n : nat => Fin n) arrow (Nat.path_nat_S (gr_nb_arrows G) m p))
             as Heq by reflexivity.
      rewrite <- Heq. clear Heq.
      pose (Hcomm := cn_comm lim_cone0 inj_arrow);
        unfold gr_edge in Hcomm; unfold gr_src in Hcomm; unfold gr_dst in Hcomm;
        simpl in Hcomm.
      exact Hcomm.
  Defined.
  Lemma ExtendMorphism (G : Graph C) (L : Limit G) :
    forall(src dst : Fin (gr_size G)),
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
  Lemma ExtendLimit (G : Graph C) (L : Limit G) :
    forall(src dst : Fin (gr_size G)),
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
        apply (cn_comm c (F1 _ (gr_nb_arrows G) 1)). }
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

End GraphLemmas.
