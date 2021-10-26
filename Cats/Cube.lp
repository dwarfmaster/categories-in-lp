
require open Cats.Universe;
require open Cats.Cat;
require open Cats.PreCube;

// Connexions
constant symbol γ : Pol → @Mph □ 2 1;
// Degeneracy
rule Comp ε (γ _) ↪ Comp ε (P ε (@Id □ 1));
// TODO not confluent
// rule C ε (γ _) ↪ C ε (P (id 1) ε);
// Associativity
rule Comp (γ $p) (P (@Id □ 1) (γ $p)) ↪ Comp (γ $p) (P (γ $p) (@Id □ 1));
// Unit
rule Comp (γ $p) (P (δ $p) (@Id □ 1)) ↪ @Id □ 1
with Comp (γ $p) (P (@Id □ 1) (δ $p)) ↪ @Id □ 1;
// Absorption
rule Comp (γ Pos) (P (δ Neg) (@Id □ 1)) ↪ Comp (δ Neg) ε
with Comp (γ Neg) (P (δ Pos) (@Id □ 1)) ↪ Comp (δ Pos) ε;

// Higher connection
symbol γ' (pol : Pol) (i n : El N) : @Mph □ (S (S (plus i n))) (S (plus i n))
     ≔ P (@Id □ i) (P (γ pol) (@Id □ n));


// Interchange
constant symbol σ : @Mph □ 2 2;
// Idempotense
rule Comp σ σ ↪ @Id □ 2
// Action
with Comp (P ε (@Id □ 1)) σ ↪ P (@Id □ 1) ε
with Comp σ (P (@Id □ 1) (δ $p)) ↪ P (δ $p) (@Id □ 1)
// Interaction with connexion
with Comp (γ $p) σ ↪ γ $p
// Displacement
with Comp (P (@Id □ 1) σ) (Comp (P σ (@Id □ 1)) (P (@Id □ 1) σ)) ↪ Comp (P σ (@Id □ 1)) (Comp (P (@Id □ 1) σ) (P σ (@Id □ 1)))
with Comp (P (@Id □ 1) (γ $p)) (Comp (P σ (@Id □ 1)) (P (@Id □ 1) σ)) ↪ Comp σ (P (γ $p) (@Id □ 1));

// Higher interchange
symbol σ' (i n : El N) : @Mph □ (S (S (plus i n))) (S (S (plus i n)))
     ≔ P (@Id □ i) (P σ (@Id □ n));
