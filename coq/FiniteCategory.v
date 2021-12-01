
From HoTT Require Import Basics.
From HoTT Require Import Categories.
Require Import Finite.

Record IsFinitePreCategory (C : PreCategory) :=
  mkFPC
    { fpc_size : nat
    ; fpc_hom_size (a b : object C) : nat
    ; fpc_equiv : object C <~> Fin fpc_size
    ; fpc_hom_equiv (a b : object C) : morphism C a b <~> Fin (fpc_hom_size a b)
    }.

Record Arrows (C : PreCategory) :=
  mkArrows
    { arr_src : object C
    ; arr_dst : object C
    ; arr_mph : morphism C arr_src arr_dst
    }.

(* TODO *)
(* Lemma FiniteArrows (C : PreCategory) : IsFinitePreCategory C -> exists n, Arrows C <~> Fin n. *)
