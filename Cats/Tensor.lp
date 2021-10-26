
require open Cats.Universe;
require open Cats.Cat;
require open Cats.PreCube;
require open Cats.Product;

// Here we implement the functor (a,b) → a ⊗ b on the precube category

// Definition
symbol ⊗ (x : PCat □ □) : Ob □ ≔ plus (π1 x) (π2 x);
symbol ⊗f {a b : PCat □ □} (f : PHom a b) : @Mph □ (⊗ a) (⊗ b) ≔ P (πf1 f) (πf2 f);

// Functor axioms
assert (a : PCat □ □) ⊢ ⊗f (Id a) ≡ @Id □ (⊗ a);
assert (a b c : PCat □ □) (f : PHom b c) (g : PHom a b) ⊢ ⊗f (f ∘ g) ≡ (⊗f f) ∘ (⊗f g);
