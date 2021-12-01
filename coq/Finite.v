
From HoTT Require Import Basics.
From HoTT Require Import Spaces.Nat.

Inductive Fin : nat -> Type :=
| F1 (n : nat) : Fin (S n)
| FS (n : nat) : Fin n -> Fin (S n).

Section FinTypes.
  Variables (n m : nat).

  Fixpoint fin_to_nat_rec {n : nat} (k : nat) (x : Fin n) : nat :=
    match x with
    | F1 _ => k
    | FS _ x => S (fin_to_nat_rec k x)
    end.
  (* Interprets Fin n as the type [0..n-1] *)
  Definition fin_to_nat {n : nat} (x : Fin n) : nat := fin_to_nat_rec 0 x.
  (* Interprets Fin n as the type [1..n] *)
  Definition fin_to_nat1 {n : nat} (x : Fin n) : nat := fin_to_nat_rec 1 x.

  Fixpoint add_fin {m : nat} (n : nat) (y : Fin m) : Fin (n + m)%nat :=
    match n with
    | O => y
    | S n => FS _ (add_fin n y)
    end.
  Fixpoint inj_fin {m : nat} (n : nat) (y : Fin m) : Fin (m + n)%nat :=
    match y with
    | F1 m => F1 (m + n)%nat
    | FS m y => FS (m + n)%nat (inj_fin n y)
    end.

  Definition pack_add (n m : nat) (e : Fin n + Fin m) : Fin (n + m)%nat :=
    match e with
    | inl x => inj_fin m x
    | inr y => add_fin n y
    end.

  Lemma unpack_add (k l : nat) (f : Fin (k + l)%nat) : Fin k + Fin l.
  Proof.
    clear n m. destruct k.
    - right. exact f.
    - induction f.
      + left. constructor.
      + exact IHf.
  Qed.

  Lemma PackEquiv : forall n m, IsEquiv (pack_add n m).
  Proof.
    Admitted.
    (* clear n m. intros n m. srapply Build_IsEquiv. *)
    (* - exact (unpack_add n m). *)
    (* - intro f. unfold unpack_add. destruct n; simpl. induction f. *)

End FinTypes.
