
require open Cats.Universe;
require open Cats.PreCube;

// Type 2
constant symbol T2 : TYPE;
constant symbol i0 : T2;
constant symbol i1 : T2;

// Objects
constant symbol CPCat' : U;
symbol CPCat : TYPE ≔ El CPCat';
symbol TFam : T2 → U;
rule TFam i0 ↪ N
with TFam i1 ↪ N;
symbol ι (i : T2) : El (TFam i) → CPCat;
symbol ρ : CPCat → T2;
symbol R (a : CPCat) : El (TFam (ρ a));
rule ρ (ι $i _) ↪ $i;
rule R (ι _ $x) ↪ $x;
rule ι (ρ $a) (R $a) ↪ $a;

// Partial cast, aka weakened R
symbol unsafe_cast (i : T2) : CPCat → El (TFam i);
rule unsafe_cast (ρ $a) $a ↪ R $a
with unsafe_cast $i (ι $i $a) ↪ $a
with ι $i (unsafe_cast $i $a) ↪ $a;

// Morphisms
constant symbol CPHom' : CPCat → CPCat → U;
symbol CPHom (a b : CPCat) : TYPE ≔ El (CPHom' a b);
symbol HFam (i : T2) : El (TFam i) → El (TFam i) → U;
rule HFam i0 $a $b ↪ HomC $a $b
with HFam i1 $a $b ↪ HomC $a $b;
symbol ι' (i : T2) (a b : El (TFam i)) : El (HFam i a b) → CPHom (ι i a) (ι i b);

// Partial cast of morphism
symbol unsafe_castF_l (a b : CPCat) : CPHom a b → El (HFam (ρ a) (R a) (unsafe_cast (ρ a) b));
symbol unsafe_castF_r (a b : CPCat) : CPHom a b → El (HFam (ρ b) (unsafe_cast (ρ b) a) (R b));
rule unsafe_castF_l _ _ (ι' _ _ _ $f) ↪ $f
with unsafe_castF_r _ _ (ι' _ _ _ $f) ↪ $f;

// Identity
symbol IdFam (i : T2) (a : El (TFam i)) : El (HFam i a a);
rule IdFam i0 $a ↪ id $a
with IdFam i1 $a ↪ id $a;
symbol CId (a : CPCat) : CPHom a a
     ≔ ι' (ρ a) (R a) (R a) (IdFam (ρ a) (R a));

// Composition
symbol CPC {a b c : CPCat} : CPHom b c → CPHom a b → CPHom a c;
symbol CFam (i : T2) {a b c : El (TFam i)} : El (HFam i b c) → El (HFam i a b) → El (HFam i a c);
rule CFam i0 $f $g ↪ C $f $g
with CFam i1 $f $g ↪ C $f $g;
rule @CPC $a $b $c $f $g ↪ ι' (ρ $b) (unsafe_cast (ρ $b) $a) (unsafe_cast (ρ $b) $c)
                               (@CFam (ρ $b) (unsafe_cast (ρ $b) $a) (R $b) (unsafe_cast (ρ $b) $c)
                                  (unsafe_castF_l $b $c $f) (unsafe_castF_r $a $b $g));

// Checks
assert a b (f : CPHom a b) ⊢ CPC (CId b) f ≡ f;
assert a b (f : CPHom a b) ⊢ CPC f (CId a) ≡ f;
