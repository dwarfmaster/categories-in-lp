
// Universe
constant symbol U : TYPE;
symbol El : U → TYPE;
unif_rule El $x ≡ El $y ↪ [ $x ≡ $y ];

// Categorical data
constant symbol C : U;
symbol tC : TYPE ≔ El C;
constant symbol Hom : El C → El C → U;
symbol tHom (c1 c2 : El C) : TYPE ≔ El (Hom c1 c2);

// Natural numbers
constant symbol N : U;
constant symbol n0 : El N;
constant symbol nsucc : El N → El N;
builtin "0" ≔ n0;
builtin "+1" ≔ nsucc;

symbol plus : El N → El N → El N;
rule plus n0 $n ↪ $n
with plus $n n0 ↪ $n
with plus (nsucc $n) $m ↪ nsucc (plus $n $m)
with plus $n (nsucc $m) ↪ nsucc (plus $n $m)
with plus $n (plus $m $k) ↪ plus (plus $n $m) $k;

assert x y z ⊢ plus x (plus y z) ≡ plus (plus x y) z;

// Vector of points
constant symbol Vect : El N → U;
constant symbol emptyV : El (Vect n0);
constant symbol concV {n : El N} : El (Vect n) → El C → El (Vect (nsucc n));
symbol v1 (x : El C) : El (Vect (nsucc n0)) ≔ concV emptyV x;

symbol last {n : El N} : El (Vect (nsucc n)) → El C;
symbol first {n : El N} : El (Vect (nsucc n)) → El C;
rule last (concV _ $x) ↪ $x
with first (concV emptyV $x) ↪ $x
with first (concV (concV $v $x) _) ↪ first (concV $v $x);

symbol concat {n m : El N} : El (Vect n) → El (Vect m) → El (Vect (plus n m));
rule concat emptyV emptyV ↪ emptyV
with concat $v1 (concat $v2 $v3) ↪ concat (concat $v1 $v2) $v3
with concat $v1 (concV $v2 $x) ↪ concV (concat $v1 $v2) $x;

assert n m k (v1 : El (Vect n)) (v2 : El (Vect m)) (v3 : El (Vect k))
     ⊢ concat (concat v1 v2) v3 ≡ concat v1 (concat v2 v3);

// Path along vector of points
constant symbol Path {n : El N} : El (Vect (nsucc n)) → U;
constant symbol idp (x : El C) : El (Path (v1 x));
constant symbol step {n : El N} {v : El (Vect (nsucc n))} {x : El C}
                     : El (Path v) → tHom (last v) x → El (Path (concV v x));

// Unbiased composition of path
symbol Comp {n : El N} {v : El (Vect (nsucc n))} (p : El (Path v))
            : El (Hom (first v) (last v));
