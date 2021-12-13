
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
Require Import Misc.
Require Import Limits.Graph.
Require Import Limits.Product.
Require Import Limits.Terminal.
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
Proof.
  destruct P. apply AllProductsFromProduct; assumption.
Qed.
