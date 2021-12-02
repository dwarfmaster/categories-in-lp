
From HoTT Require Import Basics.
From HoTT Require Import Categories.
Require Import Finite.

Local Open Scope morphism_scope.

Record Graph {C : PreCategory} :=
  mkGraph
    { gr_size : nat
    ; gr_vertex : Fin gr_size -> object C
    ; gr_nb_arrows : nat
    ; gr_edges : Fin gr_nb_arrows
               -> exists(src dst : Fin gr_size), morphism C (gr_vertex src) (gr_vertex dst)
    }.
Arguments Graph C : clear implicits.

Definition gr_src {C : PreCategory} (G : Graph C) (n : Fin (gr_nb_arrows G)) : Fin (gr_size G) :=
  proj1 (gr_edges G n).
Definition gr_dst {C : PreCategory} (G : Graph C) (n : Fin (gr_nb_arrows G)) : Fin (gr_size G) :=
  proj1 (proj2 (gr_edges G n)).
Definition gr_src' {C : PreCategory} (G : Graph C) (n : Fin (gr_nb_arrows G)) : object C :=
  gr_vertex G (gr_src G n).
Definition gr_dst' {C : PreCategory} (G : Graph C) (n : Fin (gr_nb_arrows G)) : object C :=
  gr_vertex G (gr_dst G n).
Definition gr_edge {C : PreCategory} (G : Graph C) (n : Fin (gr_nb_arrows G))
  : morphism C (gr_src' G n) (gr_dst' G n) :=
  proj2 (proj2 (gr_edges G n)).

Record Cone {C : PreCategory} {G : Graph C} :=
  mkCone
    { cn_top  : object C
    ; cn_side : forall(n : Fin (gr_size G)), morphism C cn_top (gr_vertex G n)
    ; cn_comm : forall(a : Fin (gr_nb_arrows G)), gr_edge G a o cn_side (gr_src G a) = cn_side (gr_dst G a)
    }.
Arguments Cone {C} G.
Record ConeMorphism {C : PreCategory} {G : Graph C} {c1 c2 : Cone G} :=
  mkCnMph
    { cnmph_mph  : morphism C (cn_top c1) (cn_top c2)
    ; cnmph_comm : forall(n : Fin (gr_size G)), cn_side c2 n o cnmph_mph = cn_side c1 n
    }.
Arguments ConeMorphism {C G} c1 c2.
Record Limit {C : PreCategory} {G : Graph C} :=
  mkLim
    { lim_cone : Cone G
    ; lim_ex   : forall(c : Cone G), ConeMorphism c lim_cone
    ; lim_uniq : forall(c : Cone G), forall(m1 m2 : ConeMorphism c lim_cone), cnmph_mph m1 = cnmph_mph m2
    }.
Arguments Limit {C} G.

Section GraphLemmas.
  Context {C : PreCategory}.

  Definition RestrictArrow (G : Graph C) : Graph C :=
    {| gr_size := gr_size G
    ;  gr_vertex := gr_vertex G
    ;  gr_nb_arrows := pred (gr_nb_arrows G)
    ;  gr_edges := fun n => gr_edges G (inj_pred n)
    |}.
  Definition RestrictCone {G : Graph C} (c : Cone G) : Cone (RestrictArrow G).
  Proof.
    srapply mkCone.
    - exact (cn_top c).
    - exact (cn_side c).
    - unfold gr_edge. unfold gr_src. unfold gr_dst. unfold RestrictArrow. simpl.
      intro a. apply (cn_comm c).
  Defined.

  Definition ExtendArrow (G : Graph C) (src dst : Fin (gr_size G))
             (f : morphism C (gr_vertex G src) (gr_vertex G dst)) : Graph C.
  Proof.
    srapply mkGraph.
    - exact (gr_size G).
    - exact (gr_vertex G).
    - exact (S (gr_nb_arrows G)).
    - intro a. destruct a.
      + exact {| proj1 := src; proj2 := {| proj1 := dst; proj2 := f |} |}.
      + apply gr_edges. apply Nat.path_nat_S in p. rewrite p. exact a.
  Defined.

  Definition EqualizerGr {a b : object C} (f g : morphism C a b) : Graph C.
  Proof.
    srapply mkGraph.
    - exact 2%nat.
    - intro x. destruct x; [ exact a | exact b ].
    - exact 2%nat.
    - intro x. destruct x.
      + exists (F1 2 1 1). exists (FS 2 1 1 (F1 1 0 1)). exact f.
      + exists (F1 2 1 1). exists (FS 2 1 1 (F1 1 0 1)). exact g.
  Defined.
  Definition Equalizer {a b : object C} (f g : morphism C a b) := Limit (EqualizerGr f g).
  Definition AllEqualizers := forall(a b : object C), forall(f g : morphism C a b), Equalizer f g.

  Lemma ExtendLimit (G : Graph C) (L : Limit (RestrictArrow G)) :
    forall(E : AllEqualizers), (exists(n : nat), gr_nb_arrows G = S n) -> Limit G.
  Proof.
    unfold AllEqualizers. intros E [na Hna]. destruct L.
    pose (fid := last_fin na). rewrite <- Hna in fid. pose (f := gr_edge G fid).
    -


End GraphLemmas.
