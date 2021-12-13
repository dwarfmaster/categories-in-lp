
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
Require Import Misc.
Require Import Limits.Graph.

Local Open Scope morphism_scope.

Section Equalizer.
  Context {C : PreCategory}.

  Definition EqualizerGr {a b : object C} (f g : morphism C a b) : Graph C (Fin 2) (Fin 2).
  Proof.
    srapply mkGraph.
    - intro x. destruct x; [ exact b | exact a ].
    - intro x. destruct x.
      + exists fin1. exists fin2. exact f.
      + exists fin1. exists fin2. exact g.
  Defined.
  Definition Equalizer {a b : object C} (f g : morphism C a b) := Limit (EqualizerGr f g).
  Definition AllEqualizers := forall(a b : object C), forall(f g : morphism C a b), Equalizer f g.
  Definition eq_obj {a b : object C} (f g : morphism C a b) (E : Equalizer f g) : object C :=
    cn_top (lim_cone E).
  Definition eq_mph {a b : object C} (f g : morphism C a b) (E : Equalizer f g)
    : morphism C (eq_obj f g E) a :=
    cn_side (lim_cone E) fin1.
  Lemma eq_mph_comm {a b : object C} (f g : morphism C a b) (E : Equalizer f g) :
    f o eq_mph f g E = g o eq_mph f g E.
  Proof.
    unfold eq_mph. destruct E. simpl.
    pose (Hcomm := cn_comm lim_cone fin1); unfold EqualizerGr in Hcomm;
      unfold gr_edge in Hcomm; unfold gr_src in Hcomm; unfold gr_dst in Hcomm;
      simpl in Hcomm.
    rewrite Hcomm; clear Hcomm.
    pose (Hcomm := cn_comm lim_cone fin2); unfold EqualizerGr in Hcomm;
      unfold gr_edge in Hcomm; unfold gr_src in Hcomm; unfold gr_dst in Hcomm;
      simpl in Hcomm.
    rewrite Hcomm; clear Hcomm.
    reflexivity.
  Qed.

  Definition eq_cone {a b c : object C} (f g : morphism C a b) (h : morphism C c a) :
    f o h = g o h -> Cone (EqualizerGr f g).
  Proof.
    intro Hcomm. srapply mkCone.
    - exact c.
    - unfold EqualizerGr. simpl. intro n. destruct n; [ exact (f o h) | exact h ].
    - unfold EqualizerGr; unfold gr_edge; unfold gr_src; unfold gr_dst; simpl.
      intro n. destruct n; simpl; [ reflexivity | symmetry; exact Hcomm ].
  Defined.
  Lemma eq_ex {a b : object C} (f g : morphism C a b) (E : Equalizer f g) :
    forall(c : object C), forall(h : morphism C c a),
      f o h = g o h -> exists(e : morphism C c (eq_obj f g E)), h = eq_mph f g E o e.
  Proof.
    intros c h Hcomm. destruct E. unfold eq_mph. simpl.
    pose (cn := eq_cone f g h Hcomm). pose (mph := lim_ex cn).
    exists(cnmph_mph mph). rewrite (cnmph_comm mph fin1).
    unfold cn; unfold eq_cone; simpl. reflexivity.
  Qed.

  Definition eq_morphism {a b c1 : object C} (f g : morphism C a b)
             (h1 : morphism C c1 a) (H1 : f o h1 = g o h1) (E : Equalizer f g)
             (m : morphism C c1 (eq_obj f g E))
    : h1 = eq_mph f g E o m -> ConeMorphism (eq_cone f g h1 H1) (lim_cone E).
  Proof.
    intro Hcomm. srapply mkCnMph; [ exact m | idtac ].
    unfold EqualizerGr; intro n; destruct n; unfold eq_cone; simpl; simpl in *.
    - rewrite Hcomm. clear Hcomm. rewrite <- associativity. f_ap. unfold eq_mph; simpl.
      pose (Hcomm := cn_comm (lim_cone E) fin2);
        unfold gr_edge in Hcomm; unfold gr_src in Hcomm; unfold gr_dst in Hcomm;
        simpl in Hcomm. rewrite Hcomm. clear Hcomm.
      destruct f0; [ apply Empty_ind; assumption | destruct u; reflexivity ].
    - rewrite Hcomm. unfold eq_mph. destruct u. reflexivity.
  Defined.
  Lemma eq_uniq {a b c : object C} (f g : morphism C a b) (h : morphism C c a) (E : Equalizer f g) :
    forall(m1 m2 : morphism C c (eq_obj f g E)),
      f o h = g o h ->
      eq_mph f g E o m1 = h ->
      eq_mph f g E o m2 = h ->
      m1 = m2.
  Proof.
    intros m1 m2 Hcn Hm1 Hm2.
    pose (mph1 := eq_morphism f g h Hcn E m1 Hm1^).
    pose (mph2 := eq_morphism f g h Hcn E m2 Hm2^).
    destruct E; unfold eq_mph in *; unfold eq_obj in *; simpl in *.
    pose (uniq := lim_uniq (eq_cone f g h Hcn) mph1 mph2).
    unfold mph1 in uniq; unfold mph2 in uniq; simpl in uniq.
    exact uniq.
  Qed.
End Equalizer.
