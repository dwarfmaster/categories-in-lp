
require open Cats.Universe;
require open Cats.Naturals;
require open Cats.Cat;
require open Cats.Functor;
require open Cats.Product;
require open Cats.Monoidal;

// See the following paper for correction proof:
//   Grandis, M., & Mauri, L. (2003). Cubical Sets And Their Site. Theory and
//   Applications of Categories, 11(), 185–211.

// Declaration of cubical category
constant symbol □ : SMonCat;
symbol Cube : Cat ≔ SMCat' □;
symbol ι_□ : N → Ob (SMCat' □);
symbol ρ_□ : Ob (SMCat' □) → N;
rule ι_□ (ρ_□ $x) ↪ $x
with ρ_□ (ι_□ $n) ↪ $n;

// Simple type with two elements
constant symbol Pol : TYPE;
constant symbol Pos : Pol;
constant symbol Neg : Pol;

// Free formulation of hom sets
constant symbol δ : Pol → @Mph (SMCat' □) (ι_□ 0) (ι_□ 1);
constant symbol ε : @Mph (SMCat' □) (ι_□ 1) (ι_□ 0);

// Monoidal structure
rule Fob (sProd □) $x ↪ ι_□ (plus (ρ_□ (π1 $x)) (ρ_□ (π2 $x)));
// The product on morphisms is free
rule ι_□ 0 ↪ sUnit □
with ρ_□ (sUnit □) ↪ 0;

// Checks
assert n m (f : @Mph Cube n m) ⊢ Fmph (sProd □) (mkPf f (Id (ι_□ 0))) ≡ f;
assert n m (f : @Mph Cube n m) ⊢ Fmph (sProd □) (mkPf (Id (ι_□ 0)) f) ≡ f;
assert (n m : Ob Cube) ⊢ Fmph (sProd □) (mkPf (Id n) (Id m)) ≡ Id (ι_□ (plus (ρ_□ n) (ρ_□ m)));

// Composition
// Constraints
rule Comp ε (δ _) ↪ Id (ι_□ 0);
// Compatibility with product
assert (a b n m i j : Ob Cube) (f1 : Mph n i) (f2 : Mph a n) (g1 : Mph m j) (g2 : Mph b m)
     ⊢ (Fmph (sProd □) (mkPf f1 g1)) ∘ (Fmph (sProd □) (mkPf f2 g2)) ≡ Fmph (sProd □) (mkPf (f1 ∘ f2) (g1 ∘ g2));
//rule Comp (@P $n $m _ _ $f1 $g1) (@P _ _ $n $m $f2 $g2) ↪ P (Comp $f1 $f2) (Comp $g1 $g2)
//with Comp $f (@P _ _ _ 0 $f2 $g) ↪ P (Comp $f $f2) $g;
// Checks
assert n ⊢ Comp (P ε (@Id □ n)) (P (δ Neg) (@Id □ n)) ≡ @Id □ n;

//// Higher faces and degeneracies
//symbol δ' (pol : Pol) (n m : Ob □) : @Mph □ (plus n m) (S (plus n m))
//     ≔ P (@Id □ n) (P (δ pol) (@Id □ m));
//symbol ε' (n i : El N) : @Mph □ (S (plus n i)) (plus n i)
//     ≔ P (@Id □ n) (P ε (@Id □ i));
