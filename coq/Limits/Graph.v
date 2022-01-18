
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
From HoTT Require Import Types.Forall.
From HoTT Require Import Types.Sigma.
Require Import Misc.

Local Open Scope morphism_scope.

Record Graph {C : PreCategory} {Size Arrows : Type} :=
  mkGraph
    { gr_vertex : Size -> object C
    ; gr_edges : Arrows
               -> exists(src dst : Size), morphism C (gr_vertex src) (gr_vertex dst)
    }.
Arguments Graph C : clear implicits.

Definition gr_src {C : PreCategory} {S A : Type} (G : Graph C S A) (n : A) : S :=
  proj1 (gr_edges G n).
Definition gr_dst {C : PreCategory} {S A : Type} (G : Graph C S A) (n : A) : S :=
  proj1 (proj2 (gr_edges G n)).
Definition gr_src' {C : PreCategory} {S A : Type} (G : Graph C S A) (n : A) : object C :=
  gr_vertex G (gr_src G n).
Definition gr_dst' {C : PreCategory} {S A : Type} (G : Graph C S A) (n : A) : object C :=
  gr_vertex G (gr_dst G n).
Definition gr_edge {C : PreCategory} {S A : Type} (G : Graph C S A) (n : A)
  : morphism C (gr_src' G n) (gr_dst' G n) :=
  proj2 (proj2 (gr_edges G n)).

Record Cone {C : PreCategory} {Size Arrows : Type} {G : Graph C Size Arrows} :=
  mkCone
    { cn_top  : object C
    ; cn_side : forall(n : Size), morphism C cn_top (gr_vertex G n)
    ; cn_comm : forall(a : Arrows), gr_edge G a o cn_side (gr_src G a) = cn_side (gr_dst G a)
    }.
Arguments Cone {C Size Arrows} G.
Record ConeMorphism {C : PreCategory} {Size Arrows : Type} {G : Graph C Size Arrows} {c1 c2 : Cone G} :=
  mkCnMph
    { cnmph_mph  : morphism C (cn_top c1) (cn_top c2)
    ; cnmph_comm : forall(n : Size), cn_side c2 n o cnmph_mph = cn_side c1 n
    }.
Arguments ConeMorphism {C Size Arrows G} c1 c2.
Record Limit {C : PreCategory} {Size Arrows : Type} {G : Graph C Size Arrows} :=
  mkLim
    { lim_cone : Cone G
    ; lim_ex   : forall(c : Cone G), ConeMorphism c lim_cone
    ; lim_uniq : forall(c : Cone G), forall(m1 m2 : ConeMorphism c lim_cone), cnmph_mph m1 = cnmph_mph m2
    }.
Arguments Limit {C Size Arrows} G.

Definition HasFiniteLimits (C : PreCategory) :=
  forall(size arrows : nat), forall(G : Graph C (Fin size) (Fin arrows)), Limit G.

Section paths.
  Context `{Funext}.
  Context {C : PreCategory}.
  Context {Size Arrows : Type}.
  Context (G : Graph C Size Arrows).

  Definition Graph_sig_T :=
    { vertex : Size -> object C
    | Arrows ->
      { src : Size
      & { dst : Size
        & morphism C (vertex src) (vertex dst) }}}.
  Lemma graph_sig : Graph_sig_T <~> Graph C Size Arrows.
  Proof. issig. Qed.

  Lemma path_Graph (G' : Graph C Size Arrows) :
    forall(p_vertex : gr_vertex G = gr_vertex G'),
    forall(p_src : forall(a : Arrows), (gr_edges G a).1 = (gr_edges G' a).1),
    forall(p_dst : forall(a : Arrows), (gr_edges G a).2.1 = (gr_edges G' a).2.1),
    (forall(a : Arrows),
        transport
          (fun V => morphism C (V (gr_edges G' a).1) (V (gr_edges G' a).2.1))
          p_vertex
          (transport (fun D => morphism C (gr_vertex G (gr_edges G' a).1) (gr_vertex G D))
            ((ap pr1 (transport_sigma (p_src a) (gr_edges G a).2) @
              transport_const (p_src a) ((gr_edges G a).2).1) @ p_dst a)
            (transport (fun S => {dst : Size & morphism C (gr_vertex G S) (gr_vertex G dst)})
               (p_src a) (gr_edges G a).2).2) = (gr_edges G' a).2.2) ->
    G = G'.
  Proof.
    destruct G, G'; simpl. intros p_vertex p_src p_dst p_arrows. path_induction.
    assert (gr_edges0 = gr_edges1) as p_edges.
    { apply path_forall; intro a. apply (path_sigma _ _ _ (p_src a)). simpl in p_arrows.
      srapply path_sigma; [ exact (ap pr1 (transport_sigma _ _) @ (transport_const _ _ @ p_dst a)) | ].
      rewrite concat_p_pp. exact (p_arrows a). }
    rewrite p_edges. reflexivity.
  Qed.

  (* Easy case *)
  Lemma path_Graph_vertex (G0 G1 : Graph C Size Empty) :
    forall(p_vertex : gr_vertex G0 = gr_vertex G1),
      G0 = G1.
  Proof.
    destruct G0, G1; simpl; intro p_vertex. path_induction.
    assert (gr_edges0 = gr_edges1) as p_edges.
    { apply path_forall. empty_ind'. }
    destruct p_edges. reflexivity.
  Qed.

  Lemma path_Cone' (c1 c2 : Cone G) :
    forall(ptop : cn_top c1 = cn_top c2),
      (transport (fun X => forall(n : Size), morphism C X (gr_vertex G n)) ptop (cn_side c1) = cn_side c2) ->
      c1 = c2.
  Proof.
    destruct c1, c2; simpl. intros; path_induction; simpl; simpl in cn_comm1.
    assert ( cn_comm0 = cn_comm1 ) as pcomm.
    { apply path_forall; intro a. apply hset_has_UIP. apply trunc_morphism. }
    destruct pcomm. reflexivity.
  Defined.
  Lemma path_Cone (c1 c2 : Cone G) :
    forall(ptop : cn_top c1 = cn_top c2),
      (forall(n : Size),
          transport (fun X => morphism C X (gr_vertex G n)) ptop (cn_side c1 n) = cn_side c2 n) ->
      c1 = c2.
  Proof.
    intros ptop pside. apply (path_Cone' _ _ ptop). apply path_forall; intro n.
    rewrite <- pside; simpl. destruct c1, c2; simpl. simpl in ptop.
    generalize dependent cn_comm1. generalize dependent cn_comm0.
    generalize dependent cn_side1. generalize dependent cn_side0.
    destruct ptop. intros; simpl. reflexivity.
  Defined.
  Lemma path_Cone_top' (c1 c2 : Cone G) :
    forall(ptop : cn_top c1 = cn_top c2),
    forall(pside : transport (fun X => forall(n : Size), morphism C X (gr_vertex G n)) ptop (cn_side c1)
              = cn_side c2),
      ap cn_top (path_Cone' c1 c2 ptop pside) = ptop.
  Proof.
    intros ptop pside. destruct c1, c2; simpl in *.
    destruct ptop, pside; simpl in *.
    destruct (path_forall cn_comm0 cn_comm1
                          (fun a => hset_has_UIP (trunc_morphism C cn_top0 (gr_dst' G a))
                                              (gr_edge G a o cn_side0 (gr_src G a))
                                              (cn_side0 (gr_dst G a))
                                              (cn_comm0 a) (cn_comm1 a))).
    reflexivity.
  Qed.
  Lemma path_Cone_top (c1 c2 : Cone G) :
    forall(ptop : cn_top c1 = cn_top c2),
    forall(pside : forall(n : Size),
         transport (fun X => morphism C X (gr_vertex G n)) ptop (cn_side c1 n)
         = cn_side c2 n),
      ap cn_top (path_Cone c1 c2 ptop pside) = ptop.
  Proof.
    intros ptop pside. unfold path_Cone. simpl.
    rewrite path_Cone_top'. reflexivity.
  Qed.

  Lemma lim_uniq_p {cn1 cn2 : Cone G} (p : cn1 = cn2) (L : Limit G)
        (mph1 : ConeMorphism cn1 (lim_cone L)) (mph2 : ConeMorphism cn2 (lim_cone L)) :
    transport
      (fun X => morphism C X (cn_top (lim_cone L)))
      (ap cn_top p)
      (cnmph_mph mph1)
    = cnmph_mph mph2.
  Proof.
    generalize dependent mph2; destruct p; intro mph2. simpl. apply lim_uniq.
  Qed.
End paths.
