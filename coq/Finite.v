
From HoTT Require Import Basics.
From HoTT Require Import Spaces.Nat.

Inductive Fin (n : nat) : Type :=
| F1 (m : nat) : n = S m -> Fin n
| FS (m : nat) : n = S m -> Fin m -> Fin n.

Section NatLemmas.
  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n => n
    end.

End NatLemmas.

Section FinTypes.

  Fixpoint fin_to_nat_rec {n : nat} (k : nat) (x : Fin n) : nat :=
    match x with
    | F1 _ _ => k
    | FS _ _ x => S (fin_to_nat_rec k x)
    end.
  (* Interprets Fin n as the type [0..n-1] *)
  Definition fin_to_nat {n : nat} (x : Fin n) : nat := fin_to_nat_rec 0 x.
  (* Interprets Fin n as the type [1..n] *)
  Definition fin_to_nat1 {n : nat} (x : Fin n) : nat := fin_to_nat_rec 1 x.

  Definition add_fin {m : nat} (n : nat) (y : Fin m) : Fin (n + m)%nat.
  Proof.
    induction n; simpl.
    - exact y.
    - eapply FS.
      + reflexivity.
      + exact IHn.
  Defined.
  Definition inj_fin {m : nat} (n : nat) (y : Fin m) : Fin (m + n)%nat.
  Proof.
    induction y; simpl in *.
    - apply (F1 _ (m + n)%nat). rewrite p. reflexivity.
    - apply (FS _ (m + n)%nat); [ idtac | exact IHy ].
      rewrite p. reflexivity.
  Defined.

  Definition inj_pred {k : nat} (y : Fin (pred k)) : Fin k.
  Proof.
    destruct k; [ exact y | idtac ].
    simpl in y. apply (FS _ k); [ reflexivity | exact y ].
  Defined.
  Fixpoint last_fin (n : nat) : Fin (S n) :=
    match n with
    | O => F1 1 0 1
    | S n => FS (S (S n)) (S n) 1 (last_fin n)
    end.

  Definition pack_add (n m : nat) (e : Fin n + Fin m) : Fin (n + m)%nat :=
    match e with
    | inl x => inj_fin m x
    | inr y => add_fin n y
    end.

  Definition unpack_add (k l : nat) (f : Fin (k + l)%nat) : Fin k + Fin l.
  Proof.
    induction k.
    - right. exact f.
    - simpl in f. destruct f.
      + left. apply (F1 _ k). reflexivity.
      + apply Nat.path_nat_S in p. rewrite <- p in f. destruct (IHk f).
        * left. apply (FS _ k); [ reflexivity | exact f0 ].
        * right. exact f0.
  Defined.

  Lemma PackEquiv : forall n m, IsEquiv (pack_add n m).
  Proof.
    Admitted.
    (* clear n m. intros n m. srapply Build_IsEquiv. *)
    (* - exact (unpack_add n m). *)
    (* - intro f. unfold unpack_add. destruct n; simpl. induction f. *)

End FinTypes.
