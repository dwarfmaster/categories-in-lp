
require open Cats.Universe;
require open Cats.Cat;

// The functor category
constant symbol Funct' : Cat → Cat → Cat;
symbol Funct (C D : Cat) : TYPE ≔ Ob (Funct' C D);
constant symbol Fob {C D : Cat} : Funct C D → Ob C → Ob D;
symbol Fmph {C D : Cat} (F : Funct C D) {a b : Ob C} : Mph a b → Mph (Fob F a) (Fob F b);
rule Fmph $F (Id $a) ↪ Id (Fob $F $a)
with Fmph $F (Comp $f $g) ↪ Comp (Fmph $F $f) (Fmph $F $g);

// Natural transformations
symbol mkNat {C D : Cat} (F G : Funct C D) (f : Π(x : Ob C), Mph (Fob F x) (Fob G x)) : Mph F G;
symbol NatF {C D : Cat} {F G : Funct C D} : Mph F G → Π(x : Ob C), Mph (Fob F x) (Fob G x);
rule NatF (mkNat _ _ $f) $x ↪ $f $x
with mkNat $F $G (λ x, @NatF _ _ $F[] $G[] $τ[] x) ↪ $τ;

// Natural identity
symbol NatId {C D : Cat} (F : Funct C D) : Mph F F ≔ mkNat F F (λ x, Id (Fob F x));
assert C D (a b : Ob C) (F : Funct C D) (f : @Mph C a b) ⊢ Comp (NatF (NatId F) b) (Fmph F f) ≡ Comp (Fmph F f) (NatF (NatId F) a);
rule NatF (@Id (Funct' _ $D) $F) $x ↪ @Id $D (Fob $F $x);

// Natural composition
symbol NatC {C D : Cat} {F G H : Funct C D} : Mph G H → Mph F G → Mph F H;
rule @NatC _ _ $F _ $H $τ $σ ↪ mkNat $F $H (λ x, NatF $τ x ∘ NatF $σ x);
assert C D (F G H L : Funct C D) (τ : Mph H L) (σ : Mph G H) (ω : Mph F G) ⊢ NatC (NatC τ σ) ω ≡ NatC τ (NatC σ ω);
assert C D (F G : Funct C D) (τ : Mph F G) ⊢ NatC (Id G) τ ≡ τ;
assert C D (F G : Funct C D) (τ : Mph F G) ⊢ NatC τ (Id F) ≡ τ;
rule @Comp (Funct' $C $D) $F $G $H $τ $σ ↪ @NatC $C $D $F $G $H $τ $σ;

// Naturality
rule Comp (@NatF _ _ $F $G $τ $b) (@Fmph _ _ $F $a $b $f) ↪ Comp (Fmph $G $f) (NatF $τ $a);
