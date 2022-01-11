
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
Require Import Misc.
Require Import Limits.Graph.
Require Import Limits.Product.
Require Import Limits.Terminal.
Require Import Limits.Pullback.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Module Slice.
  Section Slice.
    Context {C : PreCategory}.
    Context {z : object C}.

    Definition s : object (C/z) -> object C := fun x => x.(CommaCategory.a).
    Definition f (ob : object (C/z)) : morphism C (s ob) z := ob.(CommaCategory.f).
    Definition m {x y : object (C/z)} : morphism (C/z) x y -> morphism C (s x) (s y) :=
      fun mph => mph.(CommaCategory.g).
  End Slice.
End Slice.

Section SliceUtilities.
  Context {C : PreCategory}.
  Import Slice.

  Definition Build_SliceObject {x y : object C} (h : morphism C x y) : object (C/y) :=
        CommaCategory.Build_object (Functor.Identity.identity C) (!y) x tt h.
  Definition Build_SliceMorphism {z : object C} (x y : object (C/z)) (h : morphism C (s x) (s y)) :
    (f y) o h = (f x) -> morphism (C/z) x y.
  Proof.
    intro H. srapply CommaCategory.Build_morphism.
    - exact h.
    - rewrite <- (contr (CommaCategory.b x)). rewrite <- (contr (CommaCategory.b y)). apply identity.
    - simpl. rewrite left_identity. rewrite H. reflexivity.
  Defined.
  Definition Build_SliceMorphism' {z : object C} (x y : object (C/z)) (h : morphism C (s x) (s y)) :
    (f y) o h = (f x) -> Core.CommaCategory.morphism x y :=
    fun H => Build_SliceMorphism x y h H.

  Lemma path_SliceObject {x y : object C} (h1 h2 : morphism C x y) :
    h1 = h2 -> Build_SliceObject h1 = Build_SliceObject h2.
  Proof.
    intro H. simple refine (CommaCategory.path_object' _ _ _ _ _); [ reflexivity | reflexivity | ].
    simpl. exact H.
  Qed.
  Lemma slice_f_injective {z : object C} (x y : object (C/z)) (H : Slice.s x = Slice.s y) :
    transport (fun s => morphism C s z) H (f x) = f y -> x = y.
  Proof.
    destruct x; destruct y; simpl in *. destruct H; simpl.
    intro Heq. rewrite Heq. clear Heq.
    destruct b; destruct b0. reflexivity.
  Qed.
  Lemma slice_f_inv_r {y : object C} (x : object (C/y)) :
    Build_SliceObject (Slice.f x) = x.
  Proof.
    simple refine (slice_f_injective _ _ _ _); [ reflexivity | reflexivity ].
  Qed.
  Lemma slice_f_inv_l {x y : object C} (m : morphism C x y) :
    Slice.f (Build_SliceObject m) = m.
  Proof. reflexivity. Qed.

  Lemma path_SliceMorphism {z : object C} (x y : object (C/z)) (h1 h2 : morphism C (s x) (s y))
        (H1 : (f y) o h1 = f x) (H2 : (f y) o h2 = f x) :
    h1 = h2 -> Build_SliceMorphism x y h1 H1 = Build_SliceMorphism x y h2 H2.
  Proof.
    intro H. apply CommaCategory.path_morphism; [ | reflexivity ]. exact H.
  Qed.
  Lemma slice_m_injective {z : object C} (x y : object (C/z)) (h1 h2 : morphism (C/z) x y) :
    m h1 = m h2 -> h1 = h2.
  Proof.
    destruct h1; simpl. intro H.
    generalize dependent p. generalize dependent p_sym. rewrite H. clear H.
    intros p_sym p. destruct h2; simpl. destruct h; destruct h0; simpl.
    assert (p = p0) as Heq by apply (center _). rewrite Heq. clear Heq.
    assert (p_sym = p_sym0) as Heq by apply (center _). rewrite Heq. clear Heq.
    reflexivity.
  Qed.
  Lemma slice_m_comm {z : object C} (x y : object (C/z)) (h : morphism (C/z) x y) :
    f y o m h = f x.
  Proof. destruct h; simpl. simpl in p_sym. rewrite left_identity in p_sym. exact p_sym. Qed.
  Lemma slice_m_comp {z : object C} (a b c : object (C/z))
        (h1 : morphism (C/z) a b) (h2 : morphism (C/z) b c) :
    m (h2 o h1) = m h2 o m h1.
  Proof. reflexivity. Qed.
  Lemma slice_m_id {z : object C} (a : object (C/z)) :
    m (identity a) = identity (s a).
  Proof. reflexivity. Qed.
End SliceUtilities.
