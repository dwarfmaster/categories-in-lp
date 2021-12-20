
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
Require Import Misc.
Require Import Limits.Graph.
Require Import Limits.Product.
Require Import Limits.Terminal.
Require Import Limits.Pullback.
Require Import Slice.Misc.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section BaseChange.
  Context {C : PreCategory}.
  Context (P : AllPullbacks C).
  Context {X Y : object C}.
  Context (f : morphism C X Y).

  Definition BaseChangeObject {a : object C} : morphism C a Y -> object C :=
    fun g => fprod_obj (P _ _ _ f g).
  Definition BaseChange' {a : object C} (g : morphism C a Y) : morphism C (BaseChangeObject g) X :=
    fpi1 (P _ _ _ f g).
  Definition BaseChange : object (C / Y) -> object (C / X) :=
    fun m => Build_SliceObject (BaseChange' (Slice.f m)).

  Let pb (s : object (C/Y)) := P _ _ _ f (Slice.f s).
  Let pb1 (s : object (C/Y)) := fpi1 (pb s).
  Let pb2 (s : object (C/Y)) := fpi2 (pb s).

  Lemma pb_comm (s d : object (C/Y)) (g : morphism (C/Y) s d) :
    f o (pb1 s) = Slice.f d o (Slice.m g o (pb2 s)).
  Proof.
    rewrite <- associativity. rewrite (CommaCategory.p_sym g). simpl.
    rewrite left_identity. apply fpi_comm.
  Qed.
  Definition pb_ex (s d : object (C/Y)) (g : morphism (C/Y) s d) :=
    fprod_ex (P _ _ _ f (Slice.f d)) _ _ (pb_comm g).

  Definition BaseChangeMorphism (s d : object (C / Y)) :
    morphism (C/Y) s d -> morphism (C/X) (BaseChange s) (BaseChange d).
  Proof.
    intro g. srapply Build_SliceMorphism; [ exact (pb_ex g).1 | ]; simpl.
    unfold BaseChange'; simpl. rewrite (fst (pb_ex g).2). reflexivity.
  Defined.

  Definition BaseChangeFunctor : Functor (C / Y) (C / X).
  Proof.
    srapply Build_Functor; [ exact BaseChange | exact BaseChangeMorphism | | ].
    - intros s d1 d2 m1 m2. apply slice_m_injective. apply fprod_uniq.
      + rewrite (fst (pb_ex (m2 o m1)).2). rewrite slice_m_comp.
        rewrite <- associativity. rewrite (fst (pb_ex m2).2).
        rewrite (fst (pb_ex m1).2). reflexivity.
      + rewrite (snd (pb_ex (m2 o m1)).2). rewrite slice_m_comp.
        rewrite <- associativity. rewrite (snd (pb_ex m2).2).
        repeat rewrite associativity. rewrite (snd (pb_ex m1).2). reflexivity.
    - intro x. apply slice_m_injective.
      apply fprod_uniq;
        [ rewrite (fst (pb_ex 1).2) | rewrite (snd (pb_ex 1).2); rewrite left_identity ];
        rewrite right_identity; reflexivity.
  Defined.

  Definition IsPiFor (F : Functor (C/X) (C/Y)) := BaseChangeFunctor -| F.
  Definition IsSigmaFor (F : Functor (C/X) (C/Y)) := F -| BaseChangeFunctor.

End BaseChange.
