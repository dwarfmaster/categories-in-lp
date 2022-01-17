
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Categories.Category.Morphisms.
From HoTT Require Import Categories.Functor.
From HoTT Require Import Categories.FunctorCategory.
From HoTT Require Import Spaces.Finite.
Require Import Misc.
Require Import Limits.Graph.
Require Import Limits.ConeCat.
Require Import Limits.Functor.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section GraphOfFunctor.
  Local Open Scope object_scope.
  Context `{Funext}.
  Context {C D : PreCategory}.
  Context {Size Arrows : Type}.
  Context (Gr : Graph (C -> D)%category Size Arrows).

  Definition pointwiseGraph (x : object C) : Graph D Size Arrows.
  Proof.
    srapply mkGraph; [ intro s; exact ((gr_vertex Gr s) _0 x) | ].
    intro a. destruct (gr_edges Gr a) as [ src [ dst tnat ] ].
    exists src. exists dst. exact (tnat x).
  Defined.

  Definition extendPointwiseCone {s d : object C} (f : morphism C s d) :
    Cone (pointwiseGraph s) -> Cone (pointwiseGraph d).
  Proof.
    intro cn. srapply mkCone; [ exact (cn_top cn) | | ].
    - intro n. refine (gr_vertex Gr n _1 f o _). exact (cn_side cn n).
    - intro a; unfold gr_edge; unfold gr_src; unfold gr_dst; simpl.
      rewrite <- associativity. rewrite commutes. rewrite associativity. f_ap.
      apply (cn_comm cn).
  Defined.
  Lemma extendPointwiseCone_comp {s d d' : object C} (f : morphism C s d) (g : morphism C d d'):
    forall(cn : Cone (pointwiseGraph s)),
      extendPointwiseCone (g o f) cn = extendPointwiseCone g (extendPointwiseCone f cn).
  Proof.
    intro cn. destruct cn. srapply path_Cone; unfold extendPointwiseCone; [ reflexivity | simpl ].
    intro n. rewrite composition_of. apply associativity.
  Qed.
  Lemma extendPointwiseCone_id {s : object C}:
    forall(cn : Cone (pointwiseGraph s)),
      extendPointwiseCone 1 cn = cn.
  Proof.
    intro cn. destruct cn. srapply path_Cone; unfold extendPointwiseCone; [ reflexivity | simpl ].
    intro n. rewrite identity_of. apply left_identity.
  Qed.
  Definition extendPointwiseCone_F {s d : object C} (f : morphism C s d) :
    Functor (ConeCategory (pointwiseGraph s)) (ConeCategory (pointwiseGraph d)).
  Proof.
    srapply Build_Functor; [ exact (extendPointwiseCone f) | | | ].
    - intros s_m d_m m. srapply mkCnMph; [ exact (cnmph_mph m) | ].
      intro n; simpl. rewrite associativity. rewrite (cnmph_comm m).
      reflexivity.
    - intros s0 d0 d'0 m1 m2; apply path_ConeMorphism; reflexivity.
    - intro x; apply path_ConeMorphism; reflexivity.
  Defined.
  Definition lim_morphism {s d : object C} (f : morphism C s d) :
    forall(cn : Cone (pointwiseGraph s)),
    forall(L : Limit (pointwiseGraph d)),
      morphism (ConeCategory (pointwiseGraph d)) (extendPointwiseCone_F f _0 cn) (lim_cone L) :=
    fun cn L => lim_ex L (extendPointwiseCone_F f _0 cn).
  Lemma extendPointwiseCone_F_comp {s d d' : object C} (f : morphism C s d) (g : morphism C d d') :
    forall(cn : Cone (pointwiseGraph s)),
      extendPointwiseCone_F (g o f) _0 cn =
        extendPointwiseCone_F g _0 (extendPointwiseCone_F f _0 cn).
  Proof.
    intro cn. srapply path_Cone; [ reflexivity | ].
    intro n; simpl. rewrite composition_of. apply associativity.
  Defined.
  Lemma extendPointwiseCone_F_id {x : object C} :
    forall(cn : Cone (pointwiseGraph x)),
      extendPointwiseCone_F 1 _0 cn = cn.
  Proof.
    intro cn. srapply path_Cone; [ reflexivity | ].
    intro n; simpl. rewrite identity_of. apply left_identity.
  Defined.

  Lemma fold_cnmph_mph_pointlim {s d d' : object C} (m1 : morphism C s d) (m2 : morphism C d d') :
    forall(pointLim : forall(x : object C), Limit (pointwiseGraph x)),
      cnmph_mph
        (lim_morphism m2 (lim_cone (pointLim d)) (pointLim d')
        o extendPointwiseCone_F m2 _1 (lim_morphism m1 (lim_cone (pointLim s)) (pointLim d))) =
        cnmph_mph (lim_morphism m2 (lim_cone (pointLim d)) (pointLim d'))
        o cnmph_mph (lim_morphism m1 (lim_cone (pointLim s)) (pointLim d)).
  Proof. intro pointLim. reflexivity. Qed.

  Definition makePointwiseFunctor : (forall x : object C, Limit (pointwiseGraph x)) -> Functor C D.
  Proof.
    intro pointLim. srapply Build_Functor.
    - intro x. exact (cn_top (lim_cone (pointLim x))).
    - intros s d m.
      exact (cnmph_mph (lim_ex (pointLim d) (extendPointwiseCone m (lim_cone (pointLim s))))).
    - intros s d d' m1 m2; simpl. rewrite <- fold_cnmph_mph_pointlim.
      rewrite <- (lim_uniq_p
                   _
                   (extendPointwiseCone_F_comp m1 m2 (lim_cone (pointLim s)))
                   (pointLim d')
                   (lim_ex (pointLim d') (extendPointwiseCone (m2 o m1) (lim_cone (pointLim s))))
                   _).
      unfold extendPointwiseCone_F_comp; rewrite path_Cone_top; simpl.
      reflexivity.
    - intro x; simpl. Unset Printing Notations.
      change (Category.Core.identity (cn_top (lim_cone (pointLim x))))
        with (cnmph_mph (CnMphId (lim_cone (pointLim x)))).
      Set Printing Notations.
      rewrite <- (lim_uniq_p
                   _
                   (extendPointwiseCone_F_id (lim_cone (pointLim x)))
                   (pointLim x)
                   (lim_ex (pointLim x) (extendPointwiseCone 1 (lim_cone (pointLim x))))
                   _).
      unfold extendPointwiseCone_F_id; rewrite path_Cone_top; simpl.
      reflexivity.
  Defined.

  (* Definition makePointwiseCone : (forall x : object C, Limit (pointwiseGraph x)) -> Cone Gr. *)
  (* Proof. *)
  (*   intro pointLim. srapply mkCone. *)
  (*   - *)

End GraphOfFunctor.
