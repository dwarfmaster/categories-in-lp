
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Categories.Category.Morphisms.
From HoTT Require Import Spaces.Finite.
From HoTT Require Import Types.Equiv.
From HoTT Require Import Types.Forall.
From HoTT Require Import Types.Sigma.

Definition fin1 : Fin 2 := inr tt.
Definition fin2 : Fin 2 := inl (inr tt).
Definition f1 : Fin 3 := inr tt.
Definition f2 : Fin 3 := inl (inr tt).
Definition f3 : Fin 3 := inl (inl (inr tt)).


Ltac empty_ind :=
  apply Empty_ind; assumption.
Ltac empty_ind' :=
  intro; empty_ind.

Ltac destruct2 n :=
  destruct n as [ [ n | [ ] ] | [ ] ];
  [ empty_ind | idtac | idtac ]; simpl.
Ltac destruct3 n :=
  destruct n as [ [ [ n | [ ] ] | [ ] ] | [ ] ];
  [ empty_ind | idtac | idtac | idtac ]; simpl.

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

(*  ___ ____   ___   *)
(* |_ _/ ___| / _ \  *)
(*  | |\___ \| | | | *)
(*  | | ___) | |_| | *)
(* |___|____/ \___/  *)
Section EqToIso.
  Local Open Scope morphism.
  Definition eqToIso {C : PreCategory} {x y : object C} (p : x = y) : morphism C x y :=
    p # 1.
  Lemma eqToIso_1 {C : PreCategory} {x : object C} : @eqToIso C x x 1 = 1.
  Proof. reflexivity. Qed.
  Lemma eqToIso_pp {C : PreCategory} {x y z : object C} (p1 : x = y) (p2 : y = z) :
    eqToIso (p1 @ p2) = eqToIso p2 o eqToIso p1.
  Proof.
    unfold eqToIso. rewrite transport_pp.
    destruct p1. rewrite right_identity. reflexivity.
  Qed.
  Lemma eqToIsoInv_r {C : PreCategory} {x y : object C} (p : x = y) :
    eqToIso p^ o eqToIso p = 1.
  Proof. rewrite <- eqToIso_pp. rewrite concat_pV. exact eqToIso_1. Qed.
  Lemma eqToIsoInv_l {C : PreCategory} {x y : object C} (p : x = y) :
    eqToIso p o eqToIso p^ = 1.
  Proof. rewrite <- eqToIso_pp. rewrite concat_Vp. exact eqToIso_1. Qed.
  Lemma eqToIsoIsIso {C : PreCategory} {x y : object C} (p : x = y) :
    IsIsomorphism (eqToIso p).
  Proof.
    srapply Build_IsIsomorphism.
    - exact (eqToIso p^).
    - apply eqToIsoInv_r.
    - apply eqToIsoInv_l.
  Qed.
  Instance eqToIsoIso (C : PreCategory) (x y : object C) (p : x = y) : IsIsomorphism (eqToIso p) :=
    eqToIsoIsIso p.
  Lemma eqToIso_V {C : PreCategory} {x y : object C} (p : x = y) :
    eqToIso p^ = (eqToIso p)^-1.
  Proof.
    apply (inverse_unique C x y (eqToIso p)).
    - apply eqToIsoInv_r.
    - apply right_inverse.
  Qed.

End EqToIso.

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

(*  _   _ ___ ____   *)
(* | | | |_ _|  _ \  *)
(* | | | || || |_) | *)
(* | |_| || ||  __/  *)
(*  \___/|___|_|     *)

Definition UIP (A : Type) := forall(x y : A), forall(p p' : x = y), p = p'.
Theorem hset_has_UIP {A : Type}: IsHSet A -> UIP A.
Proof. intros H x y p p'. destruct (H x y p p'). exact center. Qed.
Theorem transport_in_hset {A : Type} (S : IsHSet A) {P : A -> Type} (x : A) (p : x = x) (w : P x) :
  transport P p w = w.
Proof.
  assert (p = 1) as Hp by (apply hset_has_UIP; assumption).
  rewrite Hp. reflexivity.
Qed.


(*  _____                      _    *)
(* |  ___|   _ _ __   _____  _| |_  *)
(* | |_ | | | | '_ \ / _ \ \/ / __| *)
(* |  _|| |_| | | | |  __/>  <| |_  *)
(* |_|   \__,_|_| |_|\___/_/\_\\__| *)

Theorem ap_funext `{Funext} {A B : Type} (P : B -> Type) (f g : A -> B) (p : f == g) (x : A) :
  ap (fun h => P (h x)) (path_forall f g p) = ap P (p x).
Proof. rewrite ap_compose'. f_ap. rewrite (ap_apply_lD _ x). f_ap. apply eisretr. Qed.
Theorem ap_funext2' {A B : Type} (P : B -> B -> Type) (f g : A -> B) (p : f = g) (x y : A) :
  ap (fun h => P (h x) (h y)) p
  = ap (fun b1 => P b1 (f y)) (apD10 p x) @ ap (fun b2 => P (g x) b2) (apD10 p y).
Proof. destruct p. reflexivity. Qed.
Theorem ap_funext2 `{Funext} {A B : Type} (P : B -> B -> Type) (f g : A -> B) (p : f == g) (x y : A) :
  ap (fun h => P (h x) (h y)) (path_forall f g p)
  = ap (fun b1 => P b1 (f y)) (p x) @ ap (fun b2 => P (g x) b2) (p y).
Proof. rewrite ap_funext2'. rewrite eisretr. reflexivity. Qed.

(*  _____            _        *)
(* | ____|__ _ _   _(_)_   __ *)
(* |  _| / _` | | | | \ \ / / *)
(* | |__| (_| | |_| | |\ V /  *)
(* |_____\__, |\__,_|_| \_/   *)
(*          |_|               *)

Lemma path_equiv_1 `{Funext} {A B : Type} {e : A <~> B} :
  @path_equiv _ A B e e 1 = 1.
Proof.
  unfold path_equiv. apply moveR_equiv_M'. reflexivity.
Qed.
Lemma path_equiv_helper `{Funext} {A B : Type} {e1 e2 : A <~> B} {p : e1 = e2 :> (A -> B)} :
  p =
  ap pr1
    (ap (fun v : A <~> B => (equiv_fun v; equiv_isequiv v))
       (ap (fun u : {f : A -> B & IsEquiv f} => {| equiv_fun := u.1; equiv_isequiv := u.2 |})
          (path_sigma_hprop (equiv_fun e1; equiv_isequiv e1) (equiv_fun e2; equiv_isequiv e2) p))).
Proof.
  rewrite <- (ap_compose
               (fun u => {| equiv_fun := u.1; equiv_isequiv := u.2 |})
               (fun v => (equiv_fun v; equiv_isequiv v))
               (path_sigma_hprop (equiv_fun e1; equiv_isequiv e1)
                                 (equiv_fun e2; equiv_isequiv e2) p)); simpl.
  rewrite <- (ap_compose (fun x : {x : _ & IsEquiv x} => (x.1; x.2)) pr1
                        (path_sigma_hprop (equiv_fun e1; equiv_isequiv e1)
                                          (equiv_fun e2; equiv_isequiv e2) p)).
  simpl. rewrite ap_pr1_path_sigma_hprop. reflexivity.
Qed.
Lemma path_equiv_V `{Funext} {A B : Type} {e1 e2 : A <~> B} {p : e1 = e2 :> (A -> B)} :
  @path_equiv _ A B e2 e1 p^ = (@path_equiv _ A B e1 e2 p)^.
Proof.
  unfold path_equiv. apply moveR_equiv_M'. unfold equiv_path_equiv; simpl.
  repeat rewrite concat_1p. repeat rewrite concat_p1.
  unfold pr1_path. repeat rewrite ap_V. f_ap.
  apply path_equiv_helper.
Qed.
Lemma path_equiv_pp `{Funext} {A B : Type} {e1 e2 e3 : A <~> B}
      {p1 : e1 = e2 :> (A -> B)} {p2 : e2 = e3 :> (A -> B)} :
  @path_equiv _ A B e1 e3 (p1 @ p2) = @path_equiv _ A B e1 e2 p1 @ @path_equiv _ A B e2 e3 p2.
Proof.
  unfold path_equiv. apply moveR_equiv_M'. unfold equiv_path_equiv; simpl.
  repeat rewrite concat_1p. repeat rewrite concat_p1.
  rewrite <- (ap_pp (fun u => {| equiv_fun := u.1; equiv_isequiv := u.2 |})
                   (path_sigma_hprop (equiv_fun e1; equiv_isequiv e1)
                                     (equiv_fun e2; equiv_isequiv e2) p1)
                   (path_sigma_hprop (equiv_fun e2; equiv_isequiv e2)
                                     (equiv_fun e3; equiv_isequiv e3) p2)).
  rewrite <- path_sigma_hprop_pp. unfold Sigma.pr1_path; simpl.
  apply path_equiv_helper.
Qed.
