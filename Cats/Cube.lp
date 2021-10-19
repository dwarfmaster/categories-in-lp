
require open Cats.Universe;
require open Cats.PreCube;

// Connexions
constant symbol γ : Pol → Hom 2 1;
// Degeneracy
rule C ε (γ _) ↪ C ε (P ε (id 1));
// TODO not confluent
// rule C ε (γ _) ↪ C ε (P (id 1) ε);
// Associativity
rule C (γ $p) (P (id 1) (γ $p)) ↪ C (γ $p) (P (γ $p) (id 1));
// Unit
rule C (γ $p) (P (δ $p) (id 1)) ↪ id 1
with C (γ $p) (P (id 1) (δ $p)) ↪ id 1;
// Absorption
rule C (γ Pos) (P (δ Neg) (id 1)) ↪ C (δ Neg) ε
with C (γ Neg) (P (δ Pos) (id 1)) ↪ C (δ Pos) ε;

// Higher connection
symbol γ' (pol : Pol) (i n : El N) : Hom (S (S (plus i n))) (S (plus i n))
     ≔ P (id i) (P (γ pol) (id n));


// Interchange
constant symbol σ : Hom 2 2;
// Idempotense
rule C σ σ ↪ id 2
// Action
with C (P ε (id 1)) σ ↪ P (id 1) ε
with C σ (P (id 1) (δ $p)) ↪ P (δ $p) (id 1)
// Interaction with connexion
with C (γ $p) σ ↪ γ $p
// Displacement
with C (P (id 1) σ) (C (P σ (id 1)) (P (id 1) σ)) ↪ C (P σ (id 1)) (C (P (id 1) σ) (P σ (id 1)))
with C (P (id 1) (γ $p)) (C (P σ (id 1)) (P (id 1) σ)) ↪ C σ (P (γ $p) (id 1));

// Higher interchange
symbol σ' (i n : El N) : Hom (S (S (plus i n))) (S (S (plus i n)))
     ≔ P (id i) (P σ (id n));
