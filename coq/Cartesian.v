
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
Require Import Misc.
Require Import Limits.Graph.
Require Import Limits.Product.
Require Import Limits.Terminal.
Require Import Limits.Pullback.
Require Import Limits.Extension.

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

Section LocallyCartesianProperties.
  Context {C : PreCategory}.
  Context {a1 a2 b : object C}.
  Context (m1 : morphism C a1 b).
  Context (m2 : morphism C a2 b).
  Let PbGr := PullbackGr m1 m2.
  Print CommaCategory.object.
  Let mkCC {x y : object C} (h : morphism C x y) : object (C/y) :=
        CommaCategory.Build_object (Functor.Identity.identity C) (!y) x tt h.
  Let ProdGr := ProductGr (mkCC m1) (mkCC m2).

  Let s {z : object C} : object (C/z) -> object C := fun x => x.(CommaCategory.a).
  Let f {z : object C} (ob : object (C/z)) : morphism C (s ob) z := ob.(CommaCategory.f).

  Definition Slice_Morphism {z : object C} (x y : object (C/z)) (h : morphism C (s x) (s y)) :
    (f y) o h = (f x) -> morphism (C/z) x y.
  Proof.
    intro H. srapply CommaCategory.Build_morphism.
    - exact h.
    - rewrite <- (contr (CommaCategory.b x)). rewrite <- (contr (CommaCategory.b y)). apply identity.
    - simpl. rewrite left_identity. rewrite H. reflexivity.
  Defined.
  Definition Slice_Morphism' {z : object C} (x y : object (C/z)) (h : morphism C (s x) (s y)) :
    (f y) o h = (f x) -> Core.CommaCategory.morphism x y.
  Proof. intro H. apply (Slice_Morphism x y h H). Defined.
  Definition unslice {z : object C} {x y : object (C/z)} : morphism (C/z) x y -> morphism C (s x) (s y).
  Proof. intro m. destruct m. exact g. Defined.
  Lemma unslice_comm {z : object C} {x y : object (C/z)} (m : morphism (C/z) x y) :
    (f y) o (unslice m) = (f x).
  Proof. destruct m. simpl. rewrite <- p. apply left_identity. Qed.

  Lemma unslice_inj {z : object C} {x y : object (C/z)} (h1 h2 : morphism (C/z) x y) :
    unslice h1 = unslice h2 -> h1 = h2.
  Proof.
    intro Hg. destruct h1; destruct h2; simpl in Hg.
    generalize dependent p_sym0. generalize dependent p0.
    rewrite <- Hg. clear g0 Hg.
    assert (h = h0) as Hh.
    { rewrite <- (contr h). rewrite <- (contr h0). reflexivity. }
    rewrite <- Hh. clear h0 Hh. intros p0 p_sym0.
    assert (p = p0) as Hp.
    { apply hset_has_UIP. apply (trunc_morphism C). }
    rewrite <- Hp. clear Hp p0.
    assert (p_sym = p_sym0) as Hp.
    { apply hset_has_UIP. apply (trunc_morphism C). }
    rewrite <- Hp. reflexivity.
  Qed.

  Definition LCConeFromPullback : Cone PbGr -> Cone ProdGr.
  Proof.
    intro cn. srapply mkCone; [ exact (mkCC (cn_side cn f3)) | idtac | empty_ind' ].
    intro n; destruct2 n.
    - refine (Slice_Morphism' (mkCC (cn_side cn f3)) (mkCC m2) _ _). apply (cn_comm cn fin1).
    - refine (Slice_Morphism' (mkCC (cn_side cn f3)) (mkCC m1) _ _). apply (cn_comm cn fin2).
  Defined.
  Definition PullbackConeFromLCCone : Cone ProdGr -> Cone PbGr.
  Proof.
    intro cn. srapply mkCone; [ exact (s (cn_top cn)) | idtac | idtac ].
    - intro n; destruct3 n; [ exact (f (cn_top cn))
                            | exact (unslice (cn_side cn fin2))
                            | exact (unslice (cn_side cn fin1))].
    - intro n; destruct2 n; unfold gr_edge; simpl.
      + apply (unslice_comm (cn_side cn fin1)).
      + apply (unslice_comm (cn_side cn fin2)).
  Defined.
  Definition AdjunctPullbackLCConeL (c1 : Cone PbGr) (c2 : Cone ProdGr) :
    ConeMorphism (LCConeFromPullback c1) c2 ->
    ConeMorphism c1 (PullbackConeFromLCCone c2).
  Proof.
    intro mph. srapply mkCnMph; [ exact (unslice (cnmph_mph mph)) | idtac ].
    intro n; destruct3 n.
    - apply (unslice_comm (cnmph_mph mph)).
    - apply (ap unslice (cnmph_comm mph fin2)).
    - apply (ap unslice (cnmph_comm mph fin1)).
  Defined.
  Definition AdjunctPullbackLCConeMorphism (c1 : Cone PbGr) (c2 : Cone ProdGr) :
    ConeMorphism c1 (PullbackConeFromLCCone c2) ->
    morphism (C/b) (cn_top (LCConeFromPullback c1)) (cn_top c2).
  Proof.
    intro mph. apply (Slice_Morphism' (mkCC (cn_side c1 f3)) (cn_top c2) (cnmph_mph mph)).
    simpl. apply (cnmph_comm mph f3).
  Defined.
  Definition AdjunctPullbackLCConeR (c1 : Cone PbGr) (c2 : Cone ProdGr) :
    ConeMorphism c1 (PullbackConeFromLCCone c2) ->
    ConeMorphism (LCConeFromPullback c1) c2.
  Proof.
    intro mph. srapply mkCnMph; [ exact (AdjunctPullbackLCConeMorphism mph) | idtac ].
    intro n; destruct2 n; apply unslice_inj; simpl.
    - apply (cnmph_comm mph f2).
    - apply (cnmph_comm mph f1).
  Defined.
  Theorem PullbackFromLocalProduct : Product (mkCC m1) (mkCC m2) -> Pullback m1 m2.
  Proof.
    intro prod. srapply mkLim; [ exact (PullbackConeFromLCCone (lim_cone prod)) | idtac | idtac ].
    - intro c. pose (cn := LCConeFromPullback c). apply AdjunctPullbackLCConeL. apply (lim_ex prod).
    - intros c m m'.
      pose (mph  := AdjunctPullbackLCConeR m). pose (mph' := AdjunctPullbackLCConeR m').
      assert (CommaCategory.g (AdjunctPullbackLCConeMorphism m)
              = CommaCategory.g (AdjunctPullbackLCConeMorphism m')) as Heq.
      { f_ap. exact (lim_uniq prod _ mph mph'). } apply Heq.
  Qed.

End LocallyCartesianProperties.

Theorem LocallyCartesianHasPullbacks {C : PreCategory} :
  IsLocallyCartesian C -> AllPullbacks C.
Proof. intro LCC. intros x y z f g. apply PullbackFromLocalProduct. apply (LCC z). Qed.
