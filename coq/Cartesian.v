
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
Require Import Misc.
Require Import Graph.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Definition IsCartesian (C : PreCategory) :=
  @Terminal C * forall(a b : object C), Product a b.

Fixpoint Vect (A : Type) (n : nat) : Type :=
  match n with
  | O => Unit
  | S n => Vect A n * A
  end.
Fixpoint get {A : Type} (n : nat) : Vect A n -> Fin n -> A :=
  match n with
  | O => fun _ (i : Fin 0) => Empty_ind (fun _ => A) i
  | S n => fun (v : Vect A (S n)) (i : Fin (S n)) =>
            match i with
            | inl i => let (v,_) := v in get n v i
            | inr tt => let (_,a) := v in a
            end
  end.
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
  destruct P. apply GraphProductsFromProduct; assumption.
Qed.
