
From HoTT Require Import Basics.
From HoTT Require Import HSet.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
Require Import Misc.
Require Import Limits.Graph.
Require Import Limits.Product.
Require Import Limits.Terminal.
Require Import Limits.Equalizer.
Require Import Limits.GraphOfFunctors.

Local Open Scope morphism_scope.

Section Pullback.
  Context {C : PreCategory}.

  Let f1 : Fin 3 := inr tt.
  Let f2 : Fin 3 := inl (inr tt).
  Let f3 : Fin 3 := inl (inl (inr tt)).

  Context {a b c : object C}.
  Context {f : morphism C a c} {g : morphism C b c}.

  Definition PullbackGr : Graph C (Fin 3) (Fin 2).
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
  Definition Pullback := Limit PullbackGr.
  Definition fprod_obj : Pullback -> object C :=
    fun lim => cn_top (lim_cone lim).
  Definition fpi1 (fprod : Pullback) : morphism C (fprod_obj fprod) a :=
    cn_side (lim_cone fprod) f1.
  Definition fpi2 (fprod : Pullback) : morphism C (fprod_obj fprod) b :=
    cn_side (lim_cone fprod) f2.
  Lemma fpi_comm (fprod : Pullback) : f o fpi1 fprod = g o fpi2 fprod.
  Proof.
    rewrite (cn_comm (lim_cone fprod) fin1).
    rewrite (cn_comm (lim_cone fprod) fin2).
    reflexivity.
  Qed.

  Definition fprod_cone (fprod : Pullback) {d : object C} :
    forall(c1 : morphism C d a) (c2 : morphism C d b),
      f o c1 = g o c2 -> Cone PullbackGr.
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
  Lemma fprod_ex (fprod : Pullback) {d : object C} :
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

  Definition fprod_mph (fprod : Pullback) {d : object C} :
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
  Lemma fprod_uniq (fprod : Pullback) {d : object C} :
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

End Pullback.

Arguments PullbackGr {C a b c} f g.
Arguments Pullback {C a b c} f g.

Definition AllPullbacks (C : PreCategory) :=
  forall(a b c : object C), forall(f : morphism C a c), forall(g : morphism C b c), Pullback f g.

Section pointwisePullback.
  Context `{Funext}.
  Context {C D : PreCategory}.
  Context {F G L : Functor C D}.
  Context (theta : NaturalTransformation F L).
  Context (tau   : NaturalTransformation G L).
  Context (x : C).
  Let Gr := pointwiseGraph (@PullbackGr (functor_category C D) F G L theta tau) x.

  Definition pwPbCone : Cone (PullbackGr (theta x) (tau x)) -> Cone Gr.
  Proof.
    intro cn. srapply mkCone; [ exact (cn_top cn) | | ].
    - intro n; pose (m := n); destruct3 n; exact (cn_side cn m).
    - intro n; pose (m := n); destruct2 n; exact (cn_comm cn m).
  Defined.
  Definition pwPbCone' : Cone Gr -> Cone (PullbackGr (theta x) (tau x)).
  Proof.
    intro cn. srapply mkCone; [ exact (cn_top cn) | | ].
    - intro n; pose (m := n); destruct3 n; exact (cn_side cn m).
    - intro n; pose (m := n); destruct2 n; exact (cn_comm cn m).
  Defined.

  Definition pwPbConeMorphismLToR (c1 : Cone Gr) (c2 : Cone (PullbackGr (theta x) (tau x))) :
    ConeMorphism (pwPbCone' c1) c2 ->
    ConeMorphism c1 (pwPbCone c2).
  Proof.
    intro mph. srapply mkCnMph; [ exact (cnmph_mph mph) | ].
    intro n; pose (m := n); destruct3 n; exact (cnmph_comm mph m).
  Defined.
  Definition pwPbConeMorphismRToL (c1 : Cone Gr) (c2 : Cone (PullbackGr (theta x) (tau x))) :
    ConeMorphism c1 (pwPbCone c2) ->
    ConeMorphism (pwPbCone' c1) c2.
  Proof.
    intro mph. srapply mkCnMph; [ exact (cnmph_mph mph) | ].
    intro n; pose (m := n); destruct3 n; exact (cnmph_comm mph m).
  Defined.

  Theorem pointwisePullback :
      Limit (PullbackGr (theta x) (tau x)) ->
      Limit (pointwiseGraph (@PullbackGr (functor_category C D) F G L theta tau) x).
  Proof.
    intro P. srapply mkLim.
    - apply pwPbCone. exact (lim_cone P).
    - intro c. apply pwPbConeMorphismLToR. apply lim_ex.
    - intros c m1 m2.
      pose (mph1 := pwPbConeMorphismRToL _ _ m1). pose (mph2 := pwPbConeMorphismRToL _ _ m2).
      apply (lim_uniq P _ mph1 mph2).
  Qed.
End pointwisePullback.

Section PullbackEqualizer.
  Context {C : PreCategory}.
  Context {a b : object C}.
  Context (f g : morphism C a b).
  Context (P : Product b b).
  Let d : morphism C b (prod_obj P) :=
        proj1 (product_ex P b (identity b) (identity b)).
  Let pack : morphism C a (prod_obj P) := proj1 (product_ex P a f g).
  Let FPEqGr := PullbackGr pack d.

  Definition PullbackConeFromEqualizer : Cone (EqualizerGr f g) -> Cone FPEqGr.
  Proof.
    intro cn. srapply mkCone; [ exact (cn_top cn) | idtac | idtac ].
    - intro n. destruct3 n; [ idtac | exact (cn_side cn fin2) | exact (cn_side cn fin1) ].
      apply (product_ex P _ (cn_side cn fin2) (cn_side cn fin2)).
    - intro n. destruct2 n; unfold gr_edge; simpl.
      + destruct (product_ex P _ (cn_side cn fin2) (cn_side cn fin2)) as [ dup [ Hpi1 Hpi2 ] ].
        unfold pack. destruct (product_ex P _ f g) as [ pk [ Hpk1 Hpk2 ] ].
        apply (product_uniq P); rewrite <- associativity; simpl;
          [ rewrite <- Hpi1; rewrite <- Hpk1
          | rewrite <- Hpi2; rewrite <- Hpk2 ].
        * apply (cn_comm cn fin2).
        * apply (cn_comm cn fin1).
      + destruct (product_ex P _ (cn_side cn fin2) (cn_side cn fin2)) as [ dup [ Hpi1 Hpi2 ] ].
        unfold d. destruct (product_ex P _ (identity b) (identity b)) as [ id [ Hid1 Hid2 ] ].
        apply (product_uniq P); rewrite <- associativity; simpl.
        * rewrite <- Hpi1. rewrite <- Hid1. apply left_identity.
        * rewrite <- Hpi2. rewrite <- Hid2. apply left_identity.
  Defined.
  Definition EqualizerConeFromPullback : Cone FPEqGr -> Cone (EqualizerGr f g).
  Proof.
    intro cn. srapply mkCone; [ exact (cn_top cn) | idtac | idtac ].
    - intro n. destruct2 n; [ exact (cn_side cn f2) | exact (cn_side cn f1) ].
    - pose (Hcomm := (cn_comm cn fin1) @ (cn_comm cn fin2)^); unfold gr_edge in Hcomm;
        unfold gr_src in Hcomm; unfold gr_dst in Hcomm; simpl in Hcomm.
      unfold d. destruct (product_ex P _ (identity b) (identity b)) as [ id [ Hid1 Hid2 ] ].
        unfold pack. destruct (product_ex P _ f g) as [ pk [ Hpk1 Hpk2 ] ].
      intro n; destruct2 n; unfold gr_edge; simpl;
        rewrite <- (left_identity C _ _ (cn_side cn f2));
        [ rewrite Hpk1; rewrite Hid1
        | rewrite Hpk2; rewrite Hid2 ];
        rewrite associativity; rewrite associativity;
        f_ap; symmetry; exact Hcomm.
  Defined.
  Definition PullbackCnMphFromEqualizer (c1 : Cone (EqualizerGr f g)) (c2 : Cone FPEqGr) :
    ConeMorphism (PullbackConeFromEqualizer c1) c2 ->
    ConeMorphism c1 (EqualizerConeFromPullback c2).
  Proof.
    intro mph. srapply mkCnMph; [ exact (cnmph_mph mph) | idtac ].
    intro n; destruct2 n.
    - apply (cnmph_comm mph f2).
    - apply (cnmph_comm mph f1).
  Defined.
  Definition EqualizerCnMphFromPullback (c1 : Cone (EqualizerGr f g)) (c2 : Cone FPEqGr) :
    ConeMorphism c1 (EqualizerConeFromPullback c2) ->
    ConeMorphism (PullbackConeFromEqualizer c1) c2.
  Proof.
    intro mph. srapply mkCnMph; [ exact (cnmph_mph mph) | idtac ].
    intro n; destruct3 n; [ idtac | apply (cnmph_comm mph fin2) | apply (cnmph_comm mph fin1) ].
    destruct (product_ex P _ (cn_side c1 fin2) (cn_side c1 fin2)) as [ dup [ Hpi1 Hpi2 ] ].
    destruct (product_ex P _ f g).2 as [ Hpk1 Hpk2 ].
    apply (product_uniq P); simpl;
      [ rewrite <- Hpi1 | rewrite <- Hpi2 ];
      rewrite <- associativity; rewrite <- (cn_comm c2 fin2); rewrite <- associativity;
      [ rewrite <- Hpk1 | rewrite <- Hpk2 ]; rewrite associativity;
      unfold gr_src; simpl; rewrite (cnmph_comm mph fin1).
    - apply (cn_comm c1 fin2).
    - apply (cn_comm c1 fin1).
  Defined.
  Theorem EqualizerFromPullback : Pullback pack d -> Equalizer f g.
  Proof.
    intro E. srapply mkLim.
    - exact (EqualizerConeFromPullback (lim_cone E)).
    - intro c. apply PullbackCnMphFromEqualizer. apply (lim_ex E).
    - intros c m1 m2.
      pose (mph1 := EqualizerCnMphFromPullback _ _ m1).
      pose (mph2 := EqualizerCnMphFromPullback _ _ m2).
      apply (lim_uniq E _ mph1 mph2).
  Qed.

End PullbackEqualizer.

Section Pullback.
  Context {C : PreCategory}.
  Context (T : Terminal C).
  Context (a b : object C).
  Let _a := terminal_ex a T.
  Let _b := terminal_ex b T.
  Let FPProdGr := PullbackGr _a _b.

  Definition PullbackConeFromProduct : Cone (ProductGr a b) -> Cone FPProdGr.
  Proof.
    intro cn. srapply mkCone; [ exact (cn_top cn) | idtac | idtac ].
    - intro n; destruct3 n; [ apply (terminal_ex _ T)
                            | apply (cn_side cn fin2)
                            | apply (cn_side cn fin1) ].
    - intro n; destruct2 n; apply (terminal_uniq _ T).
  Defined.
  Definition ProductConeFromPullback : Cone FPProdGr -> Cone (ProductGr a b).
  Proof.
    intro cn. srapply mkCone; [ exact (cn_top cn) | idtac | empty_ind' ].
    intro n; destruct2 n; [ apply (cn_side cn f2) | apply (cn_side cn f1) ].
  Defined.
  Definition ProductCnMphFromPullback (c1 : Cone (ProductGr a b)) (c2 : Cone FPProdGr) :
    ConeMorphism (PullbackConeFromProduct c1) c2 ->
    ConeMorphism c1 (ProductConeFromPullback c2).
  Proof.
    intro mph. srapply mkCnMph; [ exact (cnmph_mph mph) | idtac ].
    intro n; destruct2 n.
    - apply (cnmph_comm mph f2).
    - apply (cnmph_comm mph f1).
  Defined.
  Definition PullbackCnMphFromProduct (c1 : Cone (ProductGr a b)) (c2 : Cone FPProdGr) :
    ConeMorphism c1 (ProductConeFromPullback c2) ->
    ConeMorphism (PullbackConeFromProduct c1) c2.
  Proof.
    intro mph. srapply mkCnMph; [ exact (cnmph_mph mph) | idtac ].
    intro n; destruct3 n.
    - apply (terminal_uniq _ T).
    - apply (cnmph_comm mph fin2).
    - apply (cnmph_comm mph fin1).
  Defined.
  Theorem ProductFromPullback : Pullback _a _b -> Product a b.
  Proof.
    intro E. srapply mkLim.
    - exact (ProductConeFromPullback (lim_cone E)).
    - intro c. apply ProductCnMphFromPullback. apply (lim_ex E).
    - intros c m1 m2.
      pose (mph1 := PullbackCnMphFromProduct _ _ m1).
      pose (mph2 := PullbackCnMphFromProduct _ _ m2).
      apply (lim_uniq E _ mph1 mph2).
  Qed.

End Pullback.
