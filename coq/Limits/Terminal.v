
From HoTT Require Import Basics.
From HoTT Require Import Categories.
From HoTT Require Import Spaces.Finite.
Require Import Misc.
Require Import Limits.Graph.

Local Open Scope morphism_scope.

Section Terminal.
  Context {C : PreCategory}.

  Definition TerminalGr : Graph C Empty Empty.
  Proof. srapply mkGraph; empty_ind'. Defined.
  Definition Terminal := Limit TerminalGr.
  Definition term_obj (T : Terminal) := cn_top (lim_cone T).

  Definition term_cone (c : object C) : Cone TerminalGr.
  Proof. srapply mkCone; [ exact c | empty_ind' | empty_ind' ]. Defined.
  Lemma terminal_ex (c : object C) (T : Terminal) : morphism C c (term_obj T).
  Proof. exact (cnmph_mph (lim_ex T (term_cone c))). Qed.

  Definition term_mph {c1 : object C} (c2 : Cone TerminalGr) (f : morphism C c1 (cn_top c2)) :
    ConeMorphism (term_cone c1) c2.
  Proof. srapply mkCnMph; [ exact f | empty_ind' ]. Defined.
  Lemma terminal_uniq (c : object C) (T : Terminal) :
    forall(f g : morphism C c (term_obj T)), f = g.
  Proof.
    intros f g. pose (f' := term_mph (lim_cone T) f). pose (g' := term_mph (lim_cone T) g).
    exact (lim_uniq T _ f' g').
  Qed.

End Terminal.

Arguments TerminalGr : clear implicits.
Arguments Terminal : clear implicits.
