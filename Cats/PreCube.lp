
require open Cats.Universe;
require open Cats.Cat;

// See the following paper for correction proof:
//   Grandis, M., & Mauri, L. (2003). Cubical Sets And Their Site. Theory and
//   Applications of Categories, 11(), 185–211.

// Natural numbers with coproduct
constant symbol N : U;
constant symbol O : El N;
constant symbol S : El N → El N;
builtin "0" ≔ O;
builtin "+1" ≔ S;

symbol plus : El N → El N → El N;
rule plus O $n ↪ $n
with plus $n O ↪ $n
with plus (S $n) $m ↪ S (plus $n $m)
with plus $n (S $m) ↪ S (plus $n $m)
with plus $n (plus $m $k) ↪ plus (plus $n $m) $k;
assert x y z ⊢ plus (plus x y) z ≡ plus x (plus y z);

// Declaration of cubical category
constant symbol □ : Cat;
rule Ob □ ↪ El N;

// Simple type with two elements
constant symbol Pol : TYPE;
constant symbol Pos : Pol;
constant symbol Neg : Pol;

// Free formulation of hom sets
constant symbol δ : Pol → @Mph □ 0 1;
constant symbol ε : @Mph □ 1 0;

// Product on arrows
symbol P {n m i j : Ob □} : @Mph □ n i → @Mph □ m j → @Mph □ (plus n m) (plus i j);
rule P $f (P $g $h) ↪ P (P $f $g) $h
with P $f (@Id □ 0) ↪ $f
with P (@Id □ 0) $f ↪ $f
with P (@Id □ $n) (@Id □ $m) ↪ @Id □ (plus $n $m);
assert n m i j (f : @Mph □ n m) (g : @Mph □ i j) ⊢ P (P f (@Id □ 0)) g ≡ P f g;
assert n m k ⊢ P (@Id □ n) (P (@Id □ m) (@Id □ k)) ≡ P (@Id □ (plus n m)) (@Id □ k);

// Composition
// Constraints
rule Comp ε (δ _) ↪ @Id □ 0;
// Compatibility with product
rule Comp (@P $n $m _ _ $f1 $g1) (@P _ _ $n $m $f2 $g2) ↪ P (Comp $f1 $f2) (Comp $g1 $g2)
with Comp $f (@P _ _ _ 0 $f2 $g) ↪ P (Comp $f $f2) $g;
// Checks
assert n ⊢ Comp (P ε (@Id □ n)) (P (δ Neg) (@Id □ n)) ≡ @Id □ n;

// Higher faces and degeneracies
symbol δ' (pol : Pol) (n m : Ob □) : @Mph □ (plus n m) (S (plus n m))
     ≔ P (@Id □ n) (P (δ pol) (@Id □ m));
symbol ε' (n i : El N) : @Mph □ (S (plus n i)) (plus n i)
     ≔ P (@Id □ n) (P ε (@Id □ i));
