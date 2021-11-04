
require open Cats.Universe;
require open Cats.Cat;
require open Cats.Naturals;
require open Cats.Functor;

// Unbiaised product
constant symbol UProd' {n : N} : (Fin n → Cat) → Cat;
symbol UProd {n : N} (f : Fin n → Cat) : TYPE ≔ Ob (UProd' f);
symbol mkUP {n : N} {f : Fin n → Cat} (objs : Π(k : Fin n), Ob (f k)) : UProd f;
symbol uπ {n : N} {f : Fin n → Cat} (k : Fin n) : UProd f → Ob (f k);
// Computation and eta-redution
rule uπ $k (mkUP $o) ↪ $o $k
with @mkUP $n $C (λ k, @uπ $n[] $C[] k $p[]) ↪ $p;

// Morphisms
symbol UPHom {n : N} {f : Fin n → Cat} (a b : UProd f) : TYPE ≔ @Mph (UProd' f) a b;
symbol mkUPf {n : N} {f : Fin n → Cat} (a b : UProd f)
             (mphs : Π(k : Fin n), @Mph (f k) (uπ k a) (uπ k b))
           : UPHom a b;
symbol uπf {n : N} {f : Fin n → Cat} (k : Fin n) {a b : UProd f} : UPHom a b → Mph (uπ k a) (uπ k b);
// Computation and eta-reduction
rule uπf $k (mkUPf _ _ $m) ↪ $m $k
with mkUPf $a $b (λ k, @uπf _ _ k $a[] $b[] $m[]) ↪ $m;

// Identity
rule @Id (UProd' $C) $x ↪ mkUPf $x $x (λ k, @Id ($C k) (uπ k $x));

// Composition
rule @Comp (UProd' _) $a _ $c $f $g ↪ mkUPf $a $c (λ k, Comp (uπf k $f) (uπf k $g));

// Check that (uπ k, uπf k) are indeed functors
assert n (k : Fin n) (C : Fin n → Cat) (x : UProd C) ⊢ uπf k (Id x) ≡ Id (uπ k x);
assert n (k : Fin n) (C : Fin n → Cat) (a b c : UProd C) (f : UPHom b c) (g : UPHom a b)
         ⊢ uπf k (f ∘ g) ≡ uπf k f ∘ uπf k g;

// Define projection functors
constant symbol UΠ {n : N} (f : Fin n → Cat) (k : Fin n) : Funct (UProd' f) (f k);
rule Fob (UΠ _ $k) $x ↪ uπ $k $x;
rule Fmph (UΠ _ $k) $f ↪ uπf $k $f;
