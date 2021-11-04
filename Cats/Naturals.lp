
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

// Injection from Fin n to Fin (n + 1)
symbol finIncr {n : N} : Fin n → Fin (nsucc n);
rule finIncr (fin0 $n) ↪ fin0 (nsucc $n)
with finIncr (finS $k) ↪ finS (finIncr $k);

// External addition
symbol finAdd {n : N} (_ : Fin n) (m : N) : Fin (plus n m);
rule finAdd $k n0 ↪ $k
with finAdd $k (nsucc $m) ↪ finAdd (finS $k) $m;

// Injection from Fin n to Fin (n + m)
symbol finShift {n : N} (m : N) : Fin n → Fin (plus n m);
rule finShift $m (fin0 $n) ↪ fin0 (plus $n $m)
with finShift $m (finS $k) ↪ finS (finShift $m $k)
with finShift n0 $k ↪ $k
with finShift (nsucc $m) $k ↪ finIncr (finShift $m $k);

// Finite to nat
symbol finToN {n : N} : Fin n → N;
rule finToN fin0 ↪ n0
with finToN (finS $x) ↪ nsucc (finToN $x);
