
require open Cats.Universe;
require open Cats.Cat;

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
rule @Id (PCat' $C $D) $a ↪ mkPf (@Id $C (π1 $a)) (@Id $D (π2 $a));

// Composition
// This should be the natural rule but it won't work:
//   @Comp (PCat' $C $D) _ _ _ (mkPf $f1 $f2) (mkPf $g1 $g2) ↪ mkPf (@Comp $C _ _ _ $f1 $g1) (@Comp $D _ _ _ $f2 $g2);
rule @Comp (PCat' _ _) _ _ _ $f $g ↪ mkPf (Comp (πf1 $f) (πf1 $g)) (Comp (πf2 $f) (πf2 $g));
assert (C D : Cat) (a b : PCat C D) (f : PHom a b) ⊢ f ∘ Id a ≡ f;
assert (C D : Cat) (a b : PCat C D) (f : PHom a b) ⊢ Id b ∘ f ≡ f;
assert (C D : Cat) (a b c d : PCat C D) (f : PHom c d) (g : PHom b c) (h : PHom a b) ⊢ (f ∘ g) ∘ h ≡ f ∘ (g ∘ h);

// Check that (π1, πf1) is indeed a functor
assert (C D : Cat) (a : PCat C D) ⊢ πf1 (Id a) ≡ @Id C (π1 a);
assert (C D : Cat) (a b c : PCat C D) (f : PHom b c) (g : PHom a b) ⊢ πf1 (f ∘ g) ≡ πf1 f ∘ πf1 g;
