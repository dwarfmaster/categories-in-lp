
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
Require Import Misc.
Require Import Limits.Graph.
Require Import Limits.Product.
Require Import Limits.Terminal.
Require Import Limits.Pullback.
Require Import Limits.Extension.
Require Import Slice.Misc.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Definition IsCartesian (C : PreCategory) :=
  Terminal C * forall(a b : object C), Product a b.

Arguments get {A n} v i.
Definition UnbiasedProductGr {C : PreCategory} {n : nat} :
  Vect (object C) n -> Graph C (Fin n) Empty
  := fun v =>
       {| gr_vertex := get v
       ;  gr_edges  := fun e => Empty_ind _ e
       |}.
Definition UnbiasedProduct {C : PreCategory} (P : IsCartesian C) {n : nat}
  (v : Vect (object C) n) : Limit (UnbiasedProductGr v).
Proof. destruct P. apply AllProductsFromProduct; assumption. Qed.

Definition IsLocallyCartesian (C : PreCategory) :=
  forall(a : object C), IsCartesian (C / a).

Module LocallyCartesianPullbacks.
  Section LCPullbacks.
    Import Slice.
    Context {C : PreCategory}.
    Context {a1 a2 b : object C}.
    Context (m1 : morphism C a1 b).
    Context (m2 : morphism C a2 b).
    Definition PbGr := PullbackGr m1 m2.
    Definition ProdGr := ProductGr (Build_SliceObject m1) (Build_SliceObject m2).

    Definition LCConeFromPullback : Cone PbGr -> Cone ProdGr.
    Proof.
      intro cn. srapply mkCone; [ exact (Build_SliceObject (cn_side cn f3)) | idtac | empty_ind' ].
      intro n; destruct2 n.
      - refine (Build_SliceMorphism' (Build_SliceObject (cn_side cn f3))
                                     (Build_SliceObject m2) _ _). apply (cn_comm cn fin1).
      - refine (Build_SliceMorphism' (Build_SliceObject (cn_side cn f3))
                                     (Build_SliceObject m1) _ _). apply (cn_comm cn fin2).
    Defined.
    Definition PullbackConeFromLCCone : Cone ProdGr -> Cone PbGr.
    Proof.
      intro cn. srapply mkCone; [ exact (s (cn_top cn)) | idtac | idtac ].
      - intro n; destruct3 n; [ exact (f (cn_top cn))
                              | exact (m (cn_side cn fin2))
                              | exact (m (cn_side cn fin1))].
      - intro n; destruct2 n; unfold gr_edge; simpl.
        + apply (slice_m_comm (cn_side cn fin1)).
        + apply (slice_m_comm (cn_side cn fin2)).
    Defined.
    Definition AdjunctPullbackLCConeL (c1 : Cone PbGr) (c2 : Cone ProdGr) :
      ConeMorphism (LCConeFromPullback c1) c2 ->
      ConeMorphism c1 (PullbackConeFromLCCone c2).
    Proof.
      intro mph. srapply mkCnMph; [ exact (m (cnmph_mph mph)) | idtac ].
      intro n; destruct3 n.
      - apply (slice_m_comm (cnmph_mph mph)).
      - apply (ap m (cnmph_comm mph fin2)).
      - apply (ap m (cnmph_comm mph fin1)).
    Defined.
    Definition AdjunctPullbackLCConeMorphism (c1 : Cone PbGr) (c2 : Cone ProdGr) :
      ConeMorphism c1 (PullbackConeFromLCCone c2) ->
      morphism (C/b) (cn_top (LCConeFromPullback c1)) (cn_top c2).
    Proof.
      intro mph. apply (Build_SliceMorphism'
                          (Build_SliceObject (cn_side c1 f3)) (cn_top c2) (cnmph_mph mph)).
      simpl. apply (cnmph_comm mph f3).
    Defined.
    Definition AdjunctPullbackLCConeR (c1 : Cone PbGr) (c2 : Cone ProdGr) :
      ConeMorphism c1 (PullbackConeFromLCCone c2) ->
      ConeMorphism (LCConeFromPullback c1) c2.
    Proof.
      intro mph. srapply mkCnMph; [ exact (AdjunctPullbackLCConeMorphism mph) | idtac ].
      intro n; destruct2 n; apply slice_m_injective; simpl.
      - apply (cnmph_comm mph f2).
      - apply (cnmph_comm mph f1).
    Defined.
    Theorem PullbackFromLocalProduct :
      Product (Build_SliceObject m1) (Build_SliceObject m2) -> Pullback m1 m2.
    Proof.
      intro prod. srapply mkLim; [ exact (PullbackConeFromLCCone (lim_cone prod)) | idtac | idtac ].
      - intro c. pose (cn := LCConeFromPullback c). apply AdjunctPullbackLCConeL. apply (lim_ex prod).
      - intros c m m'.
        pose (mph  := AdjunctPullbackLCConeR m). pose (mph' := AdjunctPullbackLCConeR m').
        assert (CommaCategory.g (AdjunctPullbackLCConeMorphism m)
                = CommaCategory.g (AdjunctPullbackLCConeMorphism m')) as Heq.
        { f_ap. exact (lim_uniq prod _ mph mph'). } apply Heq.
    Defined.
  End LCPullbacks.
End LocallyCartesianPullbacks.

Theorem LocallyCartesianPullbacks {C : PreCategory} (LCC : IsLocallyCartesian C)
        {a b c : object C} (f : morphism C a c) (g : morphism C b c) :
  exists(P : Pullback f g),
    fprod_obj P = Slice.s (prod_obj (snd (LCC c) (Build_SliceObject f) (Build_SliceObject g))).
Proof.
  exists(LocallyCartesianPullbacks.PullbackFromLocalProduct (snd (LCC c)
                                                            (Build_SliceObject f)
                                                            (Build_SliceObject g))).
  reflexivity.
Qed.

Theorem LocallyCartesianHasPullbacks {C : PreCategory} :
  IsLocallyCartesian C -> AllPullbacks C.
Proof.
  intro LCC. intros x y z f g. apply LocallyCartesianPullbacks. assumption.
Defined.

Module LocallyCartesianFromPullbacks.
  Section LCPullbacks.
    Import Slice.
    Context {C : PreCategory}.
    Context {c : object C}.
    Context {a b : object (C/c)}.

    Let ProdGr := ProductGr a b.
    Let PbGr := PullbackGr (f a) (f b).

    Definition PullbackConeFromLCCone : Cone ProdGr -> Cone PbGr.
    Proof.
      intro cn. srapply mkCone.
      - exact (s (cn_top cn)).
      - intro n; destruct3 n.
        + exact (f (cn_top cn)).
        + apply m. exact (cn_side cn fin2).
        + apply m. exact (cn_side cn fin1).
      - intro n; destruct2 n.
        + apply (slice_m_comm (cn_side cn fin1)).
        + apply (slice_m_comm (cn_side cn fin2)).
    Defined.
    Definition LCConeFromPullback : Cone PbGr -> Cone ProdGr.
    Proof.
      intro cn. srapply mkCone; [ exact (Build_SliceObject (cn_side cn f3)) | idtac | empty_ind' ].
      intro n; destruct2 n.
      - apply (Build_SliceMorphism' (Build_SliceObject (cn_side cn f3)) b (cn_side cn f2)). simpl.
        apply (cn_comm cn fin1).
      - apply (Build_SliceMorphism' (Build_SliceObject (cn_side cn f3)) a (cn_side cn f1)). simpl.
        apply (cn_comm cn fin2).
    Defined.
    Definition AdjunctPullbackLCConeL (c1 : Cone ProdGr) (c2 : Cone PbGr) :
      ConeMorphism (PullbackConeFromLCCone c1) c2 ->
      ConeMorphism c1 (LCConeFromPullback c2).
    Proof.
      intro mph. srapply mkCnMph.
      - apply (Build_SliceMorphism' (cn_top c1) (cn_top (LCConeFromPullback c2)) (cnmph_mph mph)).
        simpl. apply (cnmph_comm mph f3).
      - intro n; destruct2 n; apply slice_m_injective; simpl.
        + apply (cnmph_comm mph f2).
        + apply (cnmph_comm mph f1).
    Defined.
    Definition AdjunctPullbackLCConeR (c1 : Cone ProdGr) (c2 : Cone PbGr) :
      ConeMorphism c1 (LCConeFromPullback c2) ->
      ConeMorphism (PullbackConeFromLCCone c1) c2.
    Proof.
      intro mph. srapply mkCnMph; [ exact (m (cnmph_mph mph)) | idtac ].
      intro n; destruct3 n.
      - apply (slice_m_comm (cnmph_mph mph)).
      - apply (ap m (cnmph_comm mph fin2)).
      - apply (ap m (cnmph_comm mph fin1)).
    Defined.
    Lemma LocalProductFromPullback : Pullback (f a) (f b) -> Product a b.
    Proof.
      intro pb. srapply mkLim.
      - exact (LCConeFromPullback (lim_cone pb)).
      - intro cn. apply AdjunctPullbackLCConeL. apply (lim_ex pb).
      - intros cn m1 m2.
        pose (mph1 := AdjunctPullbackLCConeR m1). pose (mph2 := AdjunctPullbackLCConeR m2).
        apply slice_m_injective. apply (lim_uniq pb _ mph1 mph2).
    Qed.

  End LCPullbacks.
End LocallyCartesianFromPullbacks.

Theorem LocallyCartesianIfPullbacks {C : PreCategory} :
  AllPullbacks C -> IsLocallyCartesian C.
Proof.
  intro P. intro x. split.
  - srapply mkLim.
    + srapply mkCone; [ exact (Build_SliceObject (identity x)) | empty_ind' | empty_ind' ].
    + intro c. srapply mkCnMph; [ simpl | empty_ind' ].
      apply (Build_SliceMorphism' (cn_top c) (Build_SliceObject (identity x)) (Slice.f (cn_top c))).
      apply left_identity.
    + intros c m1 m2. apply slice_m_injective.
      rewrite <- (left_identity C _ _ (Slice.m (cnmph_mph m1))).
      rewrite <- (left_identity C _ _ (Slice.m (cnmph_mph m2))).
      rewrite (slice_m_comm (cnmph_mph m1)). rewrite (slice_m_comm (cnmph_mph m2)).
      reflexivity.
  - intros a b. apply LocallyCartesianFromPullbacks.LocalProductFromPullback. apply P.
Qed.

Theorem LCC_CompleteIffTerminal {C : PreCategory} (LCC : IsLocallyCartesian C) :
  Terminal C <-> HasFiniteLimits C.
Proof.
  split; intro H.
  - apply AllLimitsFromPullbackAndTerminal; try assumption.
    apply LocallyCartesianHasPullbacks. exact LCC.
  - exact (H 0%nat 0%nat (TerminalGr C)).
Qed.

Module LCCHasLocalPullbacks.
  Section LCCHasLocalPullbacks.
    Context `{Funext}.
    Context {C : PreCategory}.
    Context (LCC : IsLocallyCartesian C).
    Context {Y : object C}.
    Context {x y z : object (C/Y)}.
    Context (f : morphism (C/Y) x z) (g : morphism (C/Y) y z).

    Definition X : object C := Slice.s z.
    Definition f_X : object (C/X) := Build_SliceObject (Slice.m f).
    Definition g_X : object (C/X) := Build_SliceObject (Slice.m g).
    Definition fXg : Product f_X g_X := snd (LCC X) f_X g_X.

    Definition PbCone : Cone (ProductGr f_X g_X) -> Cone (PullbackGr f g).
    Proof.
      intro cn. srapply mkCone.
      - srapply Build_SliceObject; [ exact (Slice.s (cn_top cn)) | ].
        exact (Slice.f z o Slice.m f o Slice.m (cn_side cn fin1)).
      - intro n; destruct3 n.
        + srapply Build_SliceMorphism; [ exact (Slice.m f o Slice.m (cn_side cn fin1)) | ].
          rewrite <- associativity. reflexivity.
        + srapply Build_SliceMorphism; [ exact (Slice.m (cn_side cn fin2)) | ].
          simpl. rewrite associativity. change (Slice.m f) with (Slice.f f_X).
          rewrite (slice_m_comm (cn_side cn fin1)). rewrite <- (slice_m_comm (cn_side cn fin2)).
          rewrite <- associativity. change (Slice.f g_X) with (Slice.m g).
          rewrite (slice_m_comm g). reflexivity.
        + srapply Build_SliceMorphism; [ exact (Slice.m (cn_side cn fin1)) | ]. simpl.
          rewrite <- (slice_m_comm f). reflexivity.
      - intro n; destruct2 n; apply slice_m_injective; simpl; try reflexivity.
        change (gr_edge (PullbackGr f g) (inr tt)) with g.
        change (Slice.m f) with (Slice.f f_X). rewrite (slice_m_comm (cn_side cn fin1)).
        rewrite <- (slice_m_comm (cn_side cn fin2)). reflexivity.
    Defined.
    Definition PdCone : Cone (PullbackGr f g) -> Cone (ProductGr f_X g_X).
    Proof.
      intro cn. srapply mkCone.
      - srapply Build_SliceObject; [ exact (Slice.s (cn_top cn)) | ].
        exact (Slice.f f_X o Slice.m (cn_side cn f1)).
      - intro n; destruct2 n.
        + srapply Build_SliceMorphism; [ exact (Slice.m (cn_side cn f2)) | ].
          simpl. rewrite <- slice_m_comp. rewrite (cn_comm cn fin1).
          rewrite <- (cn_comm cn fin2). reflexivity.
        + srapply Build_SliceMorphism; [ exact (Slice.m (cn_side cn f1)) | ].
          reflexivity.
      - intro n. empty_ind.
    Defined.

    Definition ConeMorphismPbToPd c1 c2 :
      ConeMorphism (PdCone c1) c2 ->
      ConeMorphism c1 (PbCone c2).
    Proof.
      intro mph. srapply mkCnMph.
      - srapply Build_SliceMorphism; [ exact (Slice.m (cnmph_mph mph)) | ].
        simpl. rewrite slice_m_comm. rewrite associativity.
        rewrite <- (slice_m_comp (cnmph_mph mph) (cn_side c2 fin1)).
        rewrite cnmph_comm. simpl. rewrite slice_m_comm. reflexivity.
      - intro n; apply slice_m_injective; rewrite slice_m_comp; destruct3 n.
        + rewrite associativity. rewrite <- (slice_m_comp (cnmph_mph mph) (cn_side c2 fin1)).
          rewrite cnmph_comm. simpl. rewrite <- slice_m_comp. rewrite (cn_comm c1 fin2).
          reflexivity.
        + rewrite <- (slice_m_comp (cnmph_mph mph) (cn_side c2 fin2)).
          rewrite cnmph_comm. reflexivity.
        + rewrite <- (slice_m_comp (cnmph_mph mph) (cn_side c2 fin1)).
          rewrite cnmph_comm. reflexivity.
    Defined.
    Definition ConeMorphismPdToPb c1 c2 :
      ConeMorphism c1 (PbCone c2) ->
      ConeMorphism (PdCone c1) c2.
    Proof.
      intro mph. srapply mkCnMph.
      - srapply Build_SliceMorphism; [ exact (Slice.m (cnmph_mph mph)) | ].
        simpl. rewrite <- (slice_m_comm (cn_side c2 fin2)). simpl.
        rewrite <- (slice_m_comp (cn_side c1 f1) f).
        rewrite (cn_comm c1 fin2). rewrite <- (cn_comm c1 fin1). rewrite slice_m_comp.
        change (gr_edge (PullbackGr f g) fin1) with g.
        rewrite <- (cnmph_comm mph f2). rewrite slice_m_comp. apply associativity.
      - intro n; apply slice_m_injective; rewrite slice_m_comp; destruct2 n.
        + rewrite <- (cnmph_comm mph f2). rewrite slice_m_comp. reflexivity.
        + rewrite <- (cnmph_comm mph f1). rewrite slice_m_comp. reflexivity.
    Defined.

    Definition PbLimit : Limit (PullbackGr f g).
    Proof.
      srapply mkLim; [ exact (PbCone (lim_cone fXg)) | | ].
      - intro cn. apply ConeMorphismPbToPd. apply lim_ex.
      - intros c m1 m2.
        pose (mph1 := ConeMorphismPdToPb m1). pose (mph2 := ConeMorphismPdToPb m2).
        pose (Huniq := lim_uniq fXg _ mph1 mph2). apply slice_m_injective.
        change (Slice.m (cnmph_mph m1)) with (Slice.m (cnmph_mph mph1)).
        change (Slice.m (cnmph_mph m2)) with (Slice.m (cnmph_mph mph2)).
        exact (ap Slice.m Huniq).
    Defined.
  End LCCHasLocalPullbacks.
End LCCHasLocalPullbacks.

Theorem LCCHasLocalPullbacks {C : PreCategory} (LCC : IsLocallyCartesian C) :
  forall(Y : object C), AllPullbacks (C/Y).
Proof.
  intros Y a b c f g. apply LCCHasLocalPullbacks.PbLimit. exact LCC.
Defined.
Arguments LCCHasLocalPullbacks [C] (LCC Y).
