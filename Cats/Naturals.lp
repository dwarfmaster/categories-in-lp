
require open Cats.Universe;

// Natural numbers
constant symbol N' : U;
symbol N : TYPE ≔ El N';
constant symbol n0 : N;
constant symbol nsucc : N → N;

// Notation
builtin "0" ≔ n0;
builtin "+1" ≔ nsucc;

// Addition
symbol plus : N → N → N;
rule plus n0 $n ↪ $n
with plus $n n0 ↪ $n
with plus (nsucc $n) $m ↪ nsucc (plus $n $m)
with plus $n (nsucc $m) ↪ nsucc (plus $n $m)
with plus $n (plus $m $k) ↪ plus (plus $n $m) $k;

// Finite types
constant symbol Fin' : N → U;
symbol Fin (n : N) : TYPE ≔ El (Fin' n);
constant symbol fin0 (n : N) : Fin (nsucc n);
constant symbol finS {n : N} : Fin n → Fin (nsucc n);

// Finite to nat
symbol finToN {n : N} : Fin n → N;
rule finToN fin0 ↪ n0
with finToN (finS $x) ↪ nsucc (finToN $x);
