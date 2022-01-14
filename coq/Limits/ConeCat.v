
From HoTT Require Import Basics.
From HoTT Require Import Types.Sigma.
From HoTT Require Import Types.Forall.
From HoTT Require Import Categories.
Require Import Misc.
Require Import Limits.Graph.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section ConeCategory.
  Context `{Funext}.
  Context {C : PreCategory}.
  Context {Size Arrows : Type}.
  Context (Gr : Graph C Size Arrows).

  Definition CnMphComp {c1 c2 c3 : Cone Gr} (m2 : ConeMorphism c2 c3) (m1 : ConeMorphism c1 c2) :
    ConeMorphism c1 c3.
  Proof.
    srapply mkCnMph; [ exact (cnmph_mph m2 o cnmph_mph m1) | ].
    intro n. rewrite <- associativity. rewrite cnmph_comm. apply cnmph_comm.
  Defined.

  Lemma path_ConeMorphism {c1 c2 : Cone Gr} (m1 m2 : ConeMorphism c1 c2) :
    cnmph_mph m1 = cnmph_mph m2 -> m1 = m2.
  Proof.
    destruct m1; destruct m2; simpl. intro Hmph.
    generalize dependent cnmph_comm0. generalize dependent cnmph_comm.
    rewrite <- Hmph. clear Hmph cnmph_mph0.
    intros comm comm0. f_ap. apply path_forall. intro n.
    apply hset_has_UIP. apply trunc_morphism.
  Qed.

  Definition CnMphId (c : Cone Gr) : ConeMorphism c c.
  Proof.
    srapply mkCnMph; [ exact 1 | ].
    intro n; apply right_identity.
  Defined.

  Lemma CnMphCompAssoc {c1 c2 c3 c4}
             (m12 : ConeMorphism c1 c2) (m23 : ConeMorphism c2 c3) (m34 : ConeMorphism c3 c4) :
    CnMphComp (CnMphComp m34 m23) m12 = CnMphComp m34 (CnMphComp m23 m12).
  Proof. apply path_ConeMorphism. simpl. apply associativity. Qed.

  Lemma CnMphCompRightId {c1 c2} (m : ConeMorphism c1 c2) : CnMphComp m (CnMphId c1) = m.
  Proof. apply path_ConeMorphism. apply right_identity. Qed.

  Lemma CnMphCompLeftId {c1 c2} (m : ConeMorphism c1 c2) : CnMphComp (CnMphId c2) m = m.
  Proof. apply path_ConeMorphism. apply left_identity. Qed.

  Definition ConeMorphism_sig_T (c1 c2 : Cone Gr) :=
    { m : morphism C (cn_top c1) (cn_top c2)
    & forall(n : Size), cn_side c2 n o m = cn_side c1 n }.
  Lemma issig_ConeMorphism (c1 c2 : Cone Gr) : ConeMorphism_sig_T c1 c2 <~> ConeMorphism c1 c2.
  Proof. issig. Qed.
  Global Instance CnMphIsHSet (c1 c2 : Cone Gr) : IsHSet (ConeMorphism c1 c2).
  Proof.
    eapply istrunc_equiv_istrunc; [ exact (issig_ConeMorphism c1 c2) | ].
    typeclasses eauto.
  Qed.

  Definition ConeCategory : PreCategory :=
    Build_PreCategory
       ConeMorphism
       CnMphId
       (@CnMphComp)
       (@CnMphCompAssoc)
       (@CnMphCompLeftId)
       (@CnMphCompRightId)
       CnMphIsHSet.
End ConeCategory.
