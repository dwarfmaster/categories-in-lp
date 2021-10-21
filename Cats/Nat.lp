
require open Cats.Universe;
require open Cats.PreCube;
require open Cats.Product;
require open Cats.Tensor;

// Underlying definition
symbol projection (n : El N) : Hom n 0;
rule projection O ↪ id 0
with @C $n _ _ (projection _) _ ↪ projection $n;

// Natural transformation
symbol deg_nat (p : PCat) : Hom (⊗ p) (π1 p) ≔ P (id (π1 p)) (projection (π2 p));

// Naturality axioms
assert (a b : PCat) (f : PHom a b) ⊢ C (deg_nat b) (⊗f f) ≡ P (πf1 f) (projection (π2 a));
assert (a b : PCat) (f : PHom a b) ⊢ C (deg_nat b) (⊗f f) ≡ C (πf1 f) (deg_nat a);
