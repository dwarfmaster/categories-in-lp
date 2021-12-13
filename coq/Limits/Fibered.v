
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
Require Import Misc.
Require Import Limits.Graph.
Require Import Limits.Product.
Require Import Limits.Equalizer.

Local Open Scope morphism_scope.

Section FiberedProduct.
  Context {C : PreCategory}.

  Let f1 : Fin 3 := inr tt.
  Let f2 : Fin 3 := inl (inr tt).
  Let f3 : Fin 3 := inl (inl (inr tt)).

  Context {a b c : object C}.
  Context {f : morphism C a c} {g : morphism C b c}.

  Definition FiberedProductGr : Graph C (Fin 3) (Fin 2).
  Proof.
    simple refine {| gr_vertex := fun f =>
                                    match f with
                                    | inr tt => a
                                    | inl (inr tt) => b
                                    | _ => c
                                    end
                  ;  gr_edges := _
                  |}.
    intro x. destruct x.
    - exists f1. exists f3. exact f.
    - exists f2. exists f3. exact g.
  Defined.
  Definition FiberedProduct := Limit FiberedProductGr.
  Definition fprod_obj : FiberedProduct -> object C :=
    fun lim => cn_top (lim_cone lim).
  Definition fpi1 (fprod : FiberedProduct) : morphism C (fprod_obj fprod) a :=
    cn_side (lim_cone fprod) f1.
  Definition fpi2 (fprod : FiberedProduct) : morphism C (fprod_obj fprod) b :=
    cn_side (lim_cone fprod) f2.
  Lemma fpi_comm (fprod : FiberedProduct) : f o fpi1 fprod = g o fpi2 fprod.
  Proof.
    rewrite (cn_comm (lim_cone fprod) fin1).
    rewrite (cn_comm (lim_cone fprod) fin2).
    reflexivity.
  Qed.

  Definition fprod_cone (fprod : FiberedProduct) {d : object C} :
    forall(c1 : morphism C d a) (c2 : morphism C d b),
      f o c1 = g o c2 -> Cone FiberedProductGr.
  Proof.
    intros c1 c2 Hcomm. srapply mkCone; [ exact d | idtac | idtac ].
    - intro n. destruct n as [ n | u ]; [ destruct n | destruct u; exact c1 ].
      + destruct f0 as [ f0 | u ]; [ empty_ind | destruct u ]. exact (f o c1).
      + destruct u. exact c2.
    - intro n; destruct n as [ n | u ];
        [ destruct n as [ n | u ]; [ empty_ind | idtac ] | idtac ];
        destruct u; simpl; try reflexivity.
      rewrite Hcomm. reflexivity.
  Defined.
  Lemma fprod_ex (fprod : FiberedProduct) {d : object C} :
    forall(c1 : morphism C d a) (c2 : morphism C d b),
      f o c1 = g o c2 ->
      exists(m : morphism C d (fprod_obj fprod)),
        fpi1 fprod o m = c1 /\ fpi2 fprod o m = c2.
  Proof.
    intros c1 c2 Hcomm. pose (cn := fprod_cone fprod c1 c2 Hcomm).
    pose (mph := lim_ex fprod cn). exists(cnmph_mph mph). split.
    - apply (cnmph_comm mph f1).
    - apply (cnmph_comm mph f2).
  Qed.

  Definition fprod_mph (fprod : FiberedProduct) {d : object C} :
    forall(m : morphism C d (fprod_obj fprod)),
    forall(c1 : morphism C d a) (c2 : morphism C d b),
    forall(Hcomm : f o c1 = g o c2),
      fpi1 fprod o m = c1 ->
      fpi2 fprod o m = c2 ->
      ConeMorphism (fprod_cone fprod c1 c2 Hcomm) (lim_cone fprod).
  Proof.
    intros m c1 c2 Hcomm Hc1 Hc2. srapply mkCnMph; [ exact m | idtac ].
    intro n; destruct n as [ [ [ e | [ ] ] | [ ] ] | [ ] ];
      [ empty_ind | idtac | idtac | idtac ];
      [ idtac | apply Hc2 | apply Hc1 ]; simpl.
    rewrite <- (cn_comm (lim_cone fprod) fin1). rewrite associativity.
    rewrite Hc2. rewrite Hcomm. reflexivity.
  Defined.
  Lemma fprod_uniq (fprod : FiberedProduct) {d : object C} :
    forall(m1 m2 : morphism C d (fprod_obj fprod)),
      fpi1 fprod o m1 = fpi1 fprod o m2 ->
      fpi2 fprod o m1 = fpi2 fprod o m2 ->
      m1 = m2.
  Proof.
    intros m1 m2 Hpi1 Hpi2.
    assert (f o (fpi1 fprod o m2) = g o (fpi2 fprod o m2)) as Hcomm.
    { rewrite <- associativity. rewrite <- associativity. f_ap. apply fpi_comm. }
    pose (mph1 := fprod_mph fprod m1 (fpi1 fprod o m2) (fpi2 fprod o m2) Hcomm Hpi1 Hpi2).
    pose (mph2 := fprod_mph fprod m2 (fpi1 fprod o m2) (fpi2 fprod o m2) Hcomm 1 1).
    apply (lim_uniq fprod _ mph1 mph2).
  Qed.

End FiberedProduct.

Arguments FiberedProductGr {C a b c} f g.
Arguments FiberedProduct {C a b c} f g.

Definition AllFibered (C : PreCategory) :=
  forall(a b c : object C), forall(f : morphism C a c), forall(g : morphism C b c), FiberedProduct f g.
