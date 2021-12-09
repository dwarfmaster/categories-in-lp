
Record Cat := mkCat
  { Obj  : Type
  ; Hom  : Obj -> Obj -> Type
  ; id   : forall(x : Obj), Hom x x
  ; comp : forall{x y z : Obj}, forall(f : Hom y z), forall(g : Hom x y), Hom x z
  ; assoc_l : forall{w x y z : Obj}, forall(f : Hom y z), forall(g : Hom x y), forall(h : Hom w x), comp (comp f g) h = comp f (comp g h)
  ; assoc_r : forall{w x y z : Obj}, forall(f : Hom y z), forall(g : Hom x y), forall(h : Hom w x), comp f (comp g h) = comp (comp f g) h
  ; id_l : forall{x y : Obj}, forall(f : Hom x y), comp (id y) f = f
  ; id_r : forall{x y : Obj}, forall(f : Hom x y), comp f (id x) = f
  ; id_id : forall(x : Obj), comp (id x) (id x) = id x
  ; homK : forall{x y : Obj}, forall{f : Hom x y}, forall(p : f = f), p = eq_refl f
  }.

Arguments Hom {c} x y.
Arguments id {c} x.
Arguments comp {c x y z} f g.
Arguments assoc_l {c w x y z} f g h.
Arguments assoc_r {c w x y z} f g h.
Arguments id_l {c x y} f.
Arguments id_r {c x y} f.
Arguments id_id {c} x.
Arguments homK {c x y f} p.

Definition Iso {C : Cat} (x y : Obj C) : Prop :=
  exists(f : Hom x y), exists(g : Hom y x), comp f g = id y /\ comp g f = id x.

Lemma equal_implies_iso {C : Cat} {x y : Obj C} :
  x = y -> Iso x y.
Proof.
  intro Heq. unfold Iso. destruct Heq.
  exists (id x). exists (id x). split; exact (id_id x).
Qed.

Record Functor (A B : Cat) := mkFun
  { Fobj  : Obj A -> Obj B
  ; Fmph  : forall{x y : Obj A}, Hom x y -> Hom (Fobj x) (Fobj y)
  ; Fid   : forall(x : Obj A), Fmph (id x) = id (Fobj x)
  ; Fcomp : forall{x y z : Obj A}, forall(f : Hom y z), forall(g : Hom x y), Fmph (comp f g) = comp (Fmph f) (Fmph g)
  }.

Record PreCategory := mkPCat
  { pObj  : Type
  ; pHom  : pObj -> pObj -> Type
  ; pid   : forall(x : pObj), pHom x x
  ; pcomp : forall{x y z : pObj}, forall(f : pHom y z), forall(g : pHom x y), pHom x z
  ; passoc_l : forall{w x y z : pObj}, forall(f : pHom y z), forall(g : pHom x y), forall(h : pHom w x), pcomp (pcomp f g) h = pcomp f (pcomp g h)
  ; pid_l : forall{x y : pObj}, forall(f : pHom x y), pcomp (pid y) f = f
  ; pid_r : forall{x y : pObj}, forall(f : pHom x y), pcomp f (pid x) = f
  ; phomK : forall{x y : pObj}, forall{f : pHom x y}, forall(p : f = f), p = eq_refl f
  }.
Definition fromPreCat (C : PreCategory) : Cat :=
  mkCat
    (pObj C)
    (pHom C)
    (pid C)
    (fun x y z => @pcomp C x y z)
    (fun w x y z => @passoc_l C w x y z)
    (fun w x y z f g h => eq_sym (@passoc_l C w x y z f g h))
    (fun x y => @pid_l C x y)
    (fun x y => @pid_r C x y)
    (fun x => @pid_l C x x (pid C x))
    (fun x y f => @phomK C x y f).

Axiom funext : forall{A B : Type}, forall(f g : A -> B), (forall x, f x = g x) -> f = g.
Record S := mkS
  { Stype : Type
  ; Sk    : forall{x : Stype}, forall(p : x = x), p = eq_refl x
  }.
Lemma Sfun (A B : S) : S.
Proof.
  apply (mkS (Stype A -> Stype B)). intros f p.
