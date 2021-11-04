
require open Cats.Universe;
require open Cats.Naturals;
require open Cats.Cat;

// Finite discrete categorys
// Identities are automatically added
constant symbol FinC' : N → Cat;
symbol FinC (n : N) : TYPE ≔ Ob (FinC' n);
rule Ob (FinC' $n) ↪ Fin $n;

// Finite linear categorys
constant symbol LinC' : N → Cat;
symbol LinC (n : N) : TYPE ≔ Ob (LinC' n);
rule Ob (LinC' $n) ↪ Fin $n;
// The morphisms are freely generated from the identities, the morphisms n → n + 1
// and the associativity
constant symbol linM {n : N} (k : Fin n) : @Mph (LinC' (nsucc n)) (finIncr k) (finS k);
// General arrows
symbol linArrow {n : N} (k : Fin n) (m : N) : @Mph (LinC' (plus n m)) (finShift m k) (finAdd k m);
rule @linArrow $n $k n0 ↪ @Id (LinC' $n) $k
with @linArrow $n $k (nsucc $m) ↪ @Comp (LinC' (nsucc (plus $n $m))) _ _ _ (linArrow (finS $k) $m) (linM (finShift $m $k));

// Checks
assert ⊢ @Comp (LinC' 5) _ _ _
          (linM (finS (finS (finS (fin0 0)))))
          (@Comp (LinC' 5) _ _ _
            (linM (finS (finS (fin0 1))))
            (linM (finS (fin0 2))))
        ≡ linArrow (finS (fin0 0)) 3;

// The arrow category
symbol Arrow' : Cat ≔ LinC' 2;
symbol Arrow : TYPE ≔ Ob Arrow';
