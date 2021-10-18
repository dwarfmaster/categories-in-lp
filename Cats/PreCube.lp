
// Universe setting for polymorphism
symbol U : TYPE;
symbol El : U → TYPE;
unif_rule El $x ≡ El $y ↪ [ $x ≡ $y ];

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

// Free formulation of hom sets
constant symbol HomC : El N → El N → U;
symbol Hom (n m : El N) : TYPE ≔ El (HomC n m);
constant symbol i0 : Hom 0 1;
constant symbol i1 : Hom 0 1;
constant symbol D  : Hom 1 0;
constant symbol id (n : El N) : Hom n n;

// Product on arrows
symbol P {n m i j : El N} : Hom n i → Hom m j → Hom (plus n m) (plus i j);
rule P $f (P $g $h) ↪ P (P $f $g) $h
with P $f (id 0) ↪ $f
with P (id 0) $f ↪ $f
with P (id $n) (id $m) ↪ id (plus $n $m);
assert n m i j (f : Hom n m) (g : Hom i j) ⊢ P (P f (id 0)) g ≡ P f g;
assert n m k ⊢ P (id n) (P (id m) (id k)) ≡ P (id (plus n m)) (id k);

// Composition
symbol C {n m k : El N} : Hom m k → Hom n m → Hom n k;
// Associativty and unitality
rule C $f (C $g $h) ↪ C (C $f $g) $h
with C (id _) $f ↪ $f
with C $f (id _) ↪ $f;
// Constraints
rule C D i0 ↪ id 0
with C D i1 ↪ id 0;
// Compatibility with product
rule C (@P $n $m _ _ $f1 $g1) (@P _ _ $n $m $f2 $g2) ↪ P (C $f1 $f2) (C $g1 $g2);
// Checks
assert n ⊢ C (P D (id n)) (P i0 (id n)) ≡ id n;

// Higher faces and degeneracies
symbol δ0 (n i : El N) : Hom (plus n i) (plus n (plus 1 i))
     ≔ P (id n) (P i0 (id i));
symbol δ1 (n i : El N) : Hom (plus n i) (plus n (plus 1 i))
     ≔ P (id n) (P i1 (id i));
symbol ε (n i : El N) : Hom (plus n (plus 1 i)) (plus n i)
     ≔ P (id n) (P D (id i));

