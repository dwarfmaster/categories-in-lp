
require open Cats.Universe;
require open Cats.PreCube;

// Product category
constant symbol PCat' : U;
symbol PCat : TYPE ≔ El PCat';
symbol mkP : El N → El N → PCat;
symbol π1 : PCat → El N;
symbol π2 : PCat → El N;
rule π1 (mkP $p _) ↪ $p
with π2 (mkP _ $p) ↪ $p
with mkP (π1 $p) (π2 $p) ↪ $p;

// Hom sets
constant symbol PHom' : PCat → PCat → U;
symbol PHom (a b : PCat) : TYPE ≔ El (PHom' a b);
symbol mkPf {a b c d : El N} : Hom a b → Hom c d → PHom (mkP a c) (mkP b d);
symbol πf1 {a b : PCat} : PHom a b → Hom (π1 a) (π1 b);
symbol πf2 {a b : PCat} : PHom a b → Hom (π2 a) (π2 b);
rule πf1 (mkPf $f _) ↪ $f
with πf2 (mkPf _ $f) ↪ $f
with mkPf (πf1 $f) (πf2 $f) ↪ $f;

// Identity
symbol Id (a : PCat) : PHom a a ≔ mkPf (id (π1 a)) (id (π2 a));

// Composition
symbol PC {a b c : PCat} : PHom b c → PHom a b → PHom a c;
// This should be the natural rule but it won't work:
//   PC (mkPf $f1 $f2) (mkPf $g1 $g2) ↪ mkPf (C $f1 $g1) (C $f2 $g2);
rule PC $f $g ↪ mkPf (C (πf1 $f) (πf1 $g)) (C (πf2 $f) (πf2 $g));
assert (a b : PCat) (f : PHom a b) ⊢ PC f (Id a) ≡ f;
assert (a b : PCat) (f : PHom a b) ⊢ PC (Id b) f ≡ f;
assert (a b c d : PCat) (f : PHom c d) (g : PHom b c) (h : PHom a b) ⊢ PC (PC f g) h ≡ PC f (PC g h);

// Check that (π1, πf1) is indeed a functor
assert (a : PCat) ⊢ πf1 (Id a) ≡ id (π1 a);
assert (a b c : PCat) (f : PHom b c) (g : PHom a b) ⊢ πf1 (PC f g) ≡ C (πf1 f) (πf1 g);
