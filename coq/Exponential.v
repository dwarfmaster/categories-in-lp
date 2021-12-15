
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
From HoTT Require Import Categories.InitialTerminalCategory.Functors.
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
End ExponentialObject.

Arguments ExponentialObject {C} (x y) P.
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
