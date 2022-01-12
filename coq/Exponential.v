
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Categories.Category.Morphisms.
From HoTT Require Import Spaces.Finite.
From HoTT Require Import Categories.InitialTerminalCategory.Functors.
From HoTT Require Import Categories.Adjoint.UnitCounit.
Require Import Misc.
Require Import Limits.Graph.
Require Import Limits.Product.
Require Import Limits.Terminal.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism.
Local Open Scope object.

Section ExponentialObject.
  Context {HF : Funext}.
  Context {C : PreCategory}.
  Context {x y : object C}.
  Context {P : forall z, Product z y}.
  Let F := ProdRFunctor y P.

  Record ExponentialObject :=
    { eobject : object C
    ; ev : morphism C (F _0 eobject) x
    ; currying {z : object C} :
       forall(e : morphism C (prod_obj (P z)) x),
         Contr { u : morphism C z eobject
                     & ev o (F _1 u) = e }
    }.
  Definition curry {z : object C} (E : ExponentialObject) :
    morphism C (prod_obj (P z)) x -> morphism C z (eobject E) :=
    fun e => proj1 (@center _ (currying E e)).
  Lemma curry_comm {z : object C} (E : ExponentialObject) :
    forall(e : morphism C (prod_obj (P z)) x),
      ev E o (F _1 (curry E e)) = e.
  Proof. intro e. exact (proj2 (@center _ (currying E e))). Qed.
  Lemma curry_uniq {z : object C} (E : ExponentialObject) :
    forall(e : morphism C (prod_obj (P z)) x),
    forall(u : morphism C z (eobject E)),
      ev E o (F _1 u) = e -> curry E e = u.
  Proof.
    intros e u H. unfold curry. destruct (currying E e) as [ [ u' Hcomm ] Huniq ]; simpl.
    apply (ap proj1 (Huniq (u;H))).
  Qed.

  Definition curry_inv {z : object C} (E : ExponentialObject) :
    morphism C z (eobject E) -> morphism C (prod_obj (P z)) x := fun g => ev E o (F _1 g).
  Lemma curry_inv_L {z : object C} (E : ExponentialObject) :
    forall(e : morphism C (prod_obj (P z)) x), curry_inv E (curry E e) = e.
  Proof. apply curry_comm. Qed.
  Lemma curry_inv_R {z : object C} (E : ExponentialObject) :
    forall(e : morphism C z (eobject E)), curry E (curry_inv E e) = e.
  Proof. intro e. apply curry_uniq. reflexivity. Qed.

  Definition curry_mph (z : object C) (E : ExponentialObject) :
    morphism set_cat
             (Build_HSet (morphism C (prod_obj (P z)) x))
             (Build_HSet (morphism C z (eobject E))) :=
    fun e => curry E e.
  Definition curry_inv_mph (z : object C) (E : ExponentialObject) :
    morphism set_cat
             (Build_HSet (morphism C z (eobject E)))
             (Build_HSet (morphism C (prod_obj (P z)) x)) :=
    fun e => curry_inv E e.
End ExponentialObject.

Arguments ExponentialObject {C} (x y) P.
Global Instance curryIso `{Funext} {C : PreCategory} {x y z : object C}
       {P : forall z, Product z y} (E : ExponentialObject x y P)
  : IsIsomorphism (curry_mph z E).
Proof.
  srapply Build_IsIsomorphism; [ exact (curry_inv_mph z E) | | ];
    apply path_forall; intro e;
    [ apply curry_inv_L | apply curry_inv_R ].
Defined.

Definition AllExponentials {C : PreCategory} (P : AllProducts C) :=
  forall(x y : object C), ExponentialObject x y (fun z => P z y).

Module ExpFunctor.
  Section ExponentialFunctor.
    Context {D C : PreCategory}.
    Context (F : Functor D (C * C^op)).
    Context (P : forall(d : object D), forall(x : object C), Product x (snd (F _0 d))).
    Context (E : forall(d : object D), ExponentialObject (fst (F _0 d)) (snd (F _0 d)) (P d)).
    Let G (d : object D) : Functor C C.
    Proof. refine (ProdRFunctor _ (P d)). Defined.

    Definition ExponentialFunctor : Functor D C.
    Proof.
      srapply Build_Functor.
      - intro d. exact (eobject (E d)).
      - intros s d m; simpl. refine (curry (E d) _). refine (_ o ev (E s) o _).
        + exact (fst (F _1 m)).
        + refine (proj1 (product_ex (P s (eobject (E s))) _ (pi1 _) (_ o pi2 (P d (eobject (E s)))))).
          exact (snd (F _1 m)).
      - intros s d1 d2 m1 m2; simpl. apply curry_uniq.
        rewrite (composition_of (G d2)).
        rewrite <- associativity. rewrite (curry_comm (E d2)).
        rewrite associativity. unfold G; unfold ProdRFunctor; simpl.
        rewrite <- (left_identity _ _ _ (pi1 (P d2 (eobject (E d1))))).
        rewrite product_ex_comm. rewrite left_identity. rewrite left_identity.
        rewrite <- (left_identity C _ _ (_ o pi2 (P d2 (eobject (E s))))).
        erewrite <- product_ex_comm. rewrite left_identity.
        instantiate (1 := P d1 (eobject (E s))). rewrite <- associativity.
        rewrite (associativity _ _ _ _ _ _ (ev (E d1))).
        pose (Hcomm := curry_comm (E d1)
                                  (fst (F _1 m1) o ev (E s)
                                      o (product_ex (P s (eobject (E s))) _
                                                    (pi1 (P d1 (eobject (E s))))
                                                    ((snd (F _1 m1) : morphism C _ _) o pi2 (P d1 (eobject (E s))))).1)).
        unfold ProdRFunctor in Hcomm; simpl in Hcomm. rewrite left_identity in Hcomm.
        rewrite Hcomm. clear Hcomm.
        rewrite <- associativity. rewrite <- associativity. rewrite (composition_of F); simpl.
        rewrite <- (left_identity _ _ _ (pi1 (P d2 (eobject (E s))))).
        rewrite (associativity _ _ _ _ _ _
                              (snd (F _1 m2) : morphism C _ _) (snd (F _1 m1) : morphism C _ _)).
        rewrite <- (product_ex_comm (P d1 (eobject (E s))) (P s (eobject (E s)))).
        rewrite <- associativity. repeat rewrite left_identity. reflexivity.
      - intro x; simpl. apply curry_uniq.
        rewrite (identity_of F). simpl. repeat rewrite left_identity. reflexivity.
    Defined.
  End ExponentialFunctor.
End ExpFunctor.

Definition ExponentialFunctor {C : PreCategory} {P : AllProducts C} (E : AllExponentials P) :
  Functor (C * C^op) C :=
  ExpFunctor.ExponentialFunctor 1%functor (fun d x => P x (snd d)) (fun d => E (fst d) (snd d)).
Definition ExponentiateFunctor {C : PreCategory} (Y : object C)
           {P : forall X, Product X Y} (E : forall X, ExponentialObject X Y P) :
  Functor C C :=
  ExpFunctor.ExponentialFunctor
    ((1, !(Y : object C^op)) o ProductLaws.Law1.inverse C)%functor
    (fun d => P) E.
Definition ExponentiatingFunctor {C : PreCategory} (X : object C)
           {P : AllProducts C} (E : forall Y, ExponentialObject X Y (fun X => P X Y)) :
  Functor C^op C :=
  ExpFunctor.ExponentialFunctor
    ((!X,1) o ProductLaws.Law1.inverse' C^op)%functor
    (fun d x => P x d) E.

Section ExponentialAdjunction.
  Context {C : PreCategory}.
  Context (Y : object C).
  Context {P : forall X, Product X Y}.
  Context (E : forall X, ExponentialObject X Y P).

  Let Fe := ExponentiateFunctor E.
  Let Fp := ProdRFunctor Y P.

  Lemma curry_comp {a b c : object C} :
    forall(m1 : morphism C (prod_obj (P a)) b),
    forall(m2 : morphism C b c),
      curry (E c) (m2 o ev (E b)) o curry (E b) m1 = curry (E c) (m2 o m1).
  Proof.
    intros m1 m2. symmetry. apply curry_uniq.
    rewrite (composition_of (ProdRFunctor Y P)). rewrite <- associativity.
    rewrite curry_comm. rewrite associativity. rewrite curry_comm.
    reflexivity.
  Qed.

  Definition exp_unit : NaturalTransformation 1 (Fe o Fp).
  Proof.
    srapply Build_NaturalTransformation.
    - intro c; simpl. apply curry. exact 1.
    - intros s d m; simpl. repeat rewrite left_identity.
      rewrite product_ex_id. rewrite right_identity.
      rewrite curry_comp. rewrite right_identity.
      symmetry. apply curry_uniq. rewrite composition_of.
      rewrite <- associativity. rewrite curry_comm.
      simpl. repeat rewrite left_identity. reflexivity.
  Defined.
  Definition exp_counit : NaturalTransformation (Fp o Fe) 1.
  Proof.
    srapply Build_NaturalTransformation.
    - intro c; simpl. apply ev.
    - intros s d m; simpl. rewrite left_identity.
      rewrite product_ex_id. rewrite right_identity.
      pose (Hcomm := curry_comm (E d) (m o ev (E s))). simpl in Hcomm.
      rewrite left_identity in Hcomm. rewrite Hcomm. reflexivity.
  Defined.

  Theorem ExponentialAdjunction : Fp -| Fe.
  Proof.
    refine {| unit := exp_unit; counit := exp_counit; |}.
    - intro c; simpl. rewrite curry_comm. reflexivity.
    - intro c; simpl. rewrite left_identity. rewrite product_ex_id.
      rewrite right_identity. rewrite curry_comp. rewrite right_identity.
      apply curry_uniq. rewrite identity_of. apply right_identity.
  Qed.

End ExponentialAdjunction.

Section ExponentialFromAdjunction.
  Context {C : PreCategory}.
  Context (Y : object C).
  Context {P : forall X, Product X Y}.
  Context {F : Functor C C}.
  Let Fp := ProdRFunctor Y P.
  Context (Adj : Fp -| F).

  Theorem ExponentialFromAdjunction : forall X, ExponentialObject X Y P.
  Proof.
    intro X. simple refine {| eobject := F _0 X; ev := counit Adj X; |}.
    intros z e. simpl in e. srapply Build_Contr.
    - exists (F _1 e o unit Adj z). rewrite composition_of. rewrite <- associativity.
      rewrite (commutes (counit Adj)). rewrite associativity.
      rewrite (unit_counit_equation_1 Adj). simpl. apply right_identity.
    - intros [ u Hu ]; simpl.
      assert (u = F _1 e o unit Adj z) as Heq.
      { rewrite <- Hu. rewrite composition_of.
        rewrite associativity. rewrite <- (commutes (unit Adj)).
        rewrite <- associativity. rewrite (unit_counit_equation_2 Adj).
        rewrite left_identity. reflexivity. }
      generalize dependent Hu. rewrite Heq. intro Hu. f_ap. apply hset_has_UIP.
      apply trunc_morphism.
  Qed.

End ExponentialFromAdjunction.
