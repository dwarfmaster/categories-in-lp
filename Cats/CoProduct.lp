
require open Cats.Universe;
require open Cats.Cat;

// Type 2
constant symbol T2 : TYPE;
constant symbol i0 : T2;
constant symbol i1 : T2;
symbol elim2 (P : T2 → U) : El (P i0) → El (P i1) → Π(i : T2), El (P i);
rule elim2 _ $p0 _ i0 ↪ $p0
with elim2 _ _ $p1 i1 ↪ $p1;

// Objects
constant symbol CPCat' : Cat → Cat → Cat;
symbol CPCat (C D : Cat) : TYPE ≔ Ob (CPCat' C D);
symbol TFam : Cat → Cat → T2 → Cat;
rule TFam $C _ i0 ↪ $C
with TFam _ $D i1 ↪ $D;
symbol ι {C D : Cat} (i : T2) : Ob (TFam C D i) → CPCat C D;
symbol ρ {C D : Cat} : CPCat C D → T2;
symbol R {C D : Cat} (a : CPCat C D) : Ob (TFam C D (ρ a));
rule ρ (ι $i _) ↪ $i;
rule R (ι _ $x) ↪ $x;
rule @ι $C $D (@ρ $C $D $a) (@R $C $D $a) ↪ $a;

// Partial cast, aka weakened R
symbol uR {C D : Cat} (i : T2) : CPCat C D → Ob (TFam C D i);
rule uR (ρ $a) $a ↪ R $a
with uR $i (ι $i $a) ↪ $a
with @ι $C $D $i (@uR $C $D $i $a) ↪ $a;

// Morphisms
symbol CPHom {C D : Cat} (a b : CPCat C D) : TYPE ≔ @Mph (CPCat' C D) a b;
symbol HFam {C D : Cat} (i : T2) : Ob (TFam C D i) → Ob (TFam C D i) → U;
rule @HFam $C _ i0 $a $b ↪ @Mph' $C $a $b
with @HFam _ $D i1 $a $b ↪ @Mph' $D $a $b;
symbol ι' {C D : Cat} (i : T2) (a b : Ob (TFam C D i)) : El (@HFam C D i a b) → @Mph (CPCat' C D) (@ι C D i a) (@ι C D i b);

// Partial cast of morphism
symbol uRf {C D : Cat} (a b : CPCat C D) (i : T2) : CPHom a b → El (@HFam C D i (uR i a) (uR i b));
rule uRf _ _ $i (ι' $i _ _ $f) ↪ $f
with uRf $a $b i0 (elim2 _ (ι' i0 (uR i0 $a) (uR i0 $b) $f) _ _) ↪ $f
with uRf $a $b i1 (elim2 _ _ (ι' i1 (uR i1 $a) (uR i1 $b) $f) _) ↪ $f;
rule elim2 (λ _, @Mph' (CPCat' _ _) _ _) (ι' i0 _ _ (uRf _ _ i0 $f)) (ι' i1 _ _ (uRf _ _ i1 $f)) _ ↪ $f;

// Identity
rule @Id (CPCat' $C $D) $a
   ↪ elim2 (λ _, @Mph' (CPCat' $C $D) $a $a)
           (ι' i0 (uR i0 $a) (uR i0 $a) (@Id $C (uR i0 $a)))
           (ι' i1 (uR i1 $a) (uR i1 $a) (@Id $D (uR i1 $a)))
           (ρ $a);

// Composition
symbol CPC {C D : Cat} {a b c : CPCat C D} : @CPHom C D b c → @CPHom C D a b → @CPHom C D a c;
rule @CPC $C $D $a $b $c $f $g
  ↪ elim2 (λ _, @Mph' (CPCat' $C $D) $a $c)
          (ι' i0 (uR i0 $a) (uR i0 $c) (@Comp $C (uR i0 $a) (uR i0 $b) (uR i0 $c) (uRf $b $c i0 $f) (uRf $a $b i0 $g)))
          (ι' i1 (uR i1 $a) (uR i1 $c) (@Comp $D (uR i1 $a) (uR i1 $b) (uR i1 $c) (uRf $b $c i1 $f) (uRf $a $b i1 $g)))
          (ρ $a);

// Checks
assert C D (a b : CPCat C D) (f : CPHom a b) ⊢ CPC (Id b) f ≡ f;
assert C D (a b : CPCat C D) (f : CPHom a b) ⊢ CPC f (Id a) ≡ f;
assert C D (a b c d : CPCat C D) (f : CPHom c d) (g : CPHom b c) (h : CPHom a b) ⊢ CPC (CPC f g) h ≡ CPC f (CPC g h);

// Make CPC cat compositon
rule @Comp (CPCat' $C $D) $a $b $c $f $g ↪ @CPC $C $D $a $b $c $f $g;
