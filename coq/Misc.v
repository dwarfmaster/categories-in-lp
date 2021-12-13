
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.


(*     _                                *)
(*    / \   _ __ _ __ _____      _____  *)
(*   / _ \ | '__| '__/ _ \ \ /\ / / __| *)
(*  / ___ \| |  | | | (_) \ V  V /\__ \ *)
(* /_/   \_\_|  |_|  \___/ \_/\_/ |___/ *)
Record Arrows {C : PreCategory} :=
  mkArrow
    { arr_src : object C
    ; arr_dst : object C
    ; arr_mph : morphism C arr_src arr_dst
    }.
Arguments Arrows C : clear implicits.
Arguments mkArrow {C arr_src arr_dst} arr_mph.


(* __     __        _                  *)
(* \ \   / /__  ___| |_ ___  _ __ ___  *)
(*  \ \ / / _ \/ __| __/ _ \| '__/ __| *)
(*   \ V /  __/ (__| || (_) | |  \__ \ *)
(*    \_/ \___|\___|\__\___/|_|  |___/ *)
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