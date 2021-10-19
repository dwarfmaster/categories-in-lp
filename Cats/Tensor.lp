
require open Cats.Universe;
require open Cats.PreCube;
require open Cats.Product;

// Here we implement the functor (a,b) → a ⊗ b on the precube category

// Definition
symbol ⊗ (x : PCat) : El N ≔ plus (π1 x) (π2 x);
symbol ⊗f {a b : PCat} (f : PHom a b) : Hom (⊗ a) (⊗ b) ≔ P (πf1 f) (πf2 f);

// Functor axioms
assert a ⊢ ⊗f (Id a) ≡ id (⊗ a);
assert a b c (f : PHom b c) (g : PHom a b) ⊢ ⊗f (PC f g) ≡ C (⊗f f) (⊗f g);
