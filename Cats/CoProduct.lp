
require open Cats.Universe;
require open Cats.Cat;

// Type 2
constant symbol T2 : TYPE;
constant symbol i0 : T2;
constant symbol i1 : T2;

// Objects
constant symbol CPCat' : Cat → Cat → Cat;
symbol CPCat (C D : Cat) : TYPE ≔ Ob (CPCat' C D);
symbol TFam : Cat → Cat → T2 → Cat;
rule TFam $C _ i0 ↪ $C
with TFam _ $D i1 ↪ $D;
symbol ι {C D : Cat} (i : T2) : Ob (TFam C D i) → CPCat C D;

// Partial cast, aka weakened R
symbol uR {C D : Cat} (i : T2) : CPCat C D → Ob (TFam C D i);
rule uR $i (ι $i $a) ↪ $a
with @ι $C $D $i (@uR $C $D $i $a) ↪ $a;

// Morphisms
symbol CPHom {C D : Cat} (a b : CPCat C D) : TYPE ≔ @Mph (CPCat' C D) a b;
symbol HFam {C D : Cat} (i : T2) : Ob (TFam C D i) → Ob (TFam C D i) → U;
rule @HFam $C _ i0 $a $b ↪ @Mph' $C $a $b
with @HFam _ $D i1 $a $b ↪ @Mph' $D $a $b;
symbol ι' {C D : Cat} (i : T2) (a b : Ob (TFam C D i)) : El (@HFam C D i a b) → @Mph (CPCat' C D) (@ι C D i a) (@ι C D i b);
// Only computes when a and b are injected from the same category
symbol elimM {C D : Cat} (a b : CPCat C D)
           : @Mph C (uR i0 a) (uR i0 b) → @Mph D (uR i1 a) (uR i1 b) → @Mph (CPCat' C D) a b;
rule elimM (ι i0 $a) (ι i0 $b) $f _ ↪ ι' i0 $a $b $f
with elimM (ι i1 $a) (ι i1 $b) _ $f ↪ ι' i1 $a $b $f;

// Partial cast of morphism
symbol uRf {C D : Cat} (a b : CPCat C D) (i : T2) : CPHom a b → El (@HFam C D i (uR i a) (uR i b));
rule uRf _ _ $i (ι' $i _ _ $f) ↪ $f
with uRf _ _ i0 (elimM _ _ $f _) ↪ $f
with uRf _ _ i1 (elimM _ _ _ $f) ↪ $f;
rule elimM $a $b (uRf $a $b i0 $f) (uRf _ _ i1 $f) ↪ $f;

// Identity
rule @Id (CPCat' $C $D) $a
   ↪ elimM $a $a (@Id $C (uR i0 $a)) (@Id $D (uR i1 $a));

// Composition
symbol CPC {C D : Cat} {a b c : CPCat C D} : @CPHom C D b c → @CPHom C D a b → @CPHom C D a c;
rule @CPC $C $D $a $b $c $f $g
  ↪ elimM $a $c
          (@Comp $C (uR i0 $a) (uR i0 $b) (uR i0 $c) (uRf $b $c i0 $f) (uRf $a $b i0 $g))
          (@Comp $D (uR i1 $a) (uR i1 $b) (uR i1 $c) (uRf $b $c i1 $f) (uRf $a $b i1 $g));

// Checks
assert C D (a b : CPCat C D) (f : CPHom a b) ⊢ CPC (Id b) f ≡ f;
assert C D (a b : CPCat C D) (f : CPHom a b) ⊢ CPC f (Id a) ≡ f;
assert C D (a b c d : CPCat C D) (f : CPHom c d) (g : CPHom b c) (h : CPHom a b) ⊢ CPC (CPC f g) h ≡ CPC f (CPC g h);

// Make CPC cat compositon
rule @Comp (CPCat' $C $D) $a $b $c $f $g ↪ @CPC $C $D $a $b $c $f $g;
