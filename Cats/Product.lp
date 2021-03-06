
require open Cats.Universe;
require open Cats.Cat;
require open Cats.Functor;

// Product category
constant symbol PCat' : Cat → Cat → Cat;
symbol PCat (C D : Cat) : TYPE ≔ Ob (PCat' C D);
symbol mkP {C D : Cat} : Ob C → Ob D → PCat C D;
symbol π1 {C D : Cat} : PCat C D → Ob C;
symbol π2 {C D : Cat} : PCat C D → Ob D;
rule π1 (mkP $p _) ↪ $p
with π2 (mkP _ $p) ↪ $p
with mkP (π1 $p) (π2 $p) ↪ $p;

// Hom sets
symbol PHom {C D : Cat} (a b : PCat C D) : TYPE ≔ @Mph (PCat' C D) a b;
symbol mkPf {C D : Cat} {a b : Ob C} {c d : Ob D} : @Mph C a b → @Mph D c d → PHom (mkP a c) (mkP b d);
symbol πf1 {C D : Cat} {a b : PCat C D} : PHom a b → @Mph C (π1 a) (π1 b);
symbol πf2 {C D : Cat} {a b : PCat C D} : PHom a b → @Mph D (π2 a) (π2 b);
rule πf1 (mkPf $f _) ↪ $f
with πf2 (mkPf _ $f) ↪ $f
with mkPf (πf1 $f) (πf2 $f) ↪ $f;

// Identity
rule mkPf (@Id $C $a) (@Id $D $b) ↪ @Id (PCat' $C $D) (mkP $a $b)
with πf1 (@Id (PCat' $C _) $a) ↪ @Id $C (π1 $a)
with πf2 (@Id (PCat' _ $D) $a) ↪ @Id $D (π2 $a);

// Composition
// This should be the natural rule but it won't work:
//   @Comp (PCat' $C $D) _ _ _ (mkPf $f1 $f2) (mkPf $g1 $g2) ↪ mkPf (@Comp $C _ _ _ $f1 $g1) (@Comp $D _ _ _ $f2 $g2);
rule mkPf (@Comp $C $a1 $b1 $c1 $f1 $g1) (@Comp $D $a2 $b2 $c2 $f2 $g2)
   ↪ @Comp (PCat' $C $D) (mkP $a1 $a2) (mkP $b1 $b2) (mkP $c1 $c2) (mkPf $f1 $g1) (mkPf $f2 $g2)
with πf1 (@Comp (PCat' _ _) _ _ _ $f $g) ↪ Comp (πf1 $f) (πf1 $g)
with πf2 (@Comp (PCat' _ _) _ _ _ $f $g) ↪ Comp (πf2 $f) (πf2 $g);
//rule @Comp (PCat' _ _) _ _ _ $f $g ↪ mkPf (Comp (πf1 $f) (πf1 $g)) (Comp (πf2 $f) (πf2 $g));
assert (C D : Cat) (a b : PCat C D) (f : PHom a b) ⊢ f ∘ Id a ≡ f;
assert (C D : Cat) (a b : PCat C D) (f : PHom a b) ⊢ Id b ∘ f ≡ f;
assert (C D : Cat) (a b c d : PCat C D) (f : PHom c d) (g : PHom b c) (h : PHom a b) ⊢ (f ∘ g) ∘ h ≡ f ∘ (g ∘ h);

// Check that (π1, πf1) is indeed a functor
assert (C D : Cat) (a : PCat C D) ⊢ πf1 (Id a) ≡ @Id C (π1 a);
assert (C D : Cat) (a b c : PCat C D) (f : PHom b c) (g : PHom a b) ⊢ πf1 (f ∘ g) ≡ πf1 f ∘ πf1 g;
// Check that (π2, πf2) is indeed a functor
assert (C D : Cat) (a : PCat C D) ⊢ πf2 (Id a) ≡ @Id D (π2 a);
assert (C D : Cat) (a b c : PCat C D) (f : PHom b c) (g : PHom a b) ⊢ πf2 (f ∘ g) ≡ πf2 f ∘ πf2 g;

// Define projections as functors
constant symbol Π1 (C D : Cat) : Funct (PCat' C D) C;
constant symbol Π2 (C D : Cat) : Funct (PCat' C D) D;
rule Fob (Π1 _ _) $x ↪ π1 $x
with Fob (Π2 _ _) $x ↪ π2 $x;
rule Fmph (Π1 _ _) $f ↪ πf1 $f
with Fmph (Π2 _ _) $f ↪ πf2 $f;
