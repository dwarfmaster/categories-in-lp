
require open Cats.Universe;

constant symbol Cat' : U;
symbol Cat : TYPE ≔ El Cat';
symbol Ob : Cat → TYPE;
unif_rule Ob $x ≡ Ob $y ↪ [ $x ≡ $y ];
symbol Mph' (C : Cat) : Ob C → Ob C → U;
unif_rule Mph' $C $a $b ≡ Mph' $C' $a' $b' ↪ [ $C ≡ $C'; $a ≡ $a'; $b ≡ $b' ];
symbol Mph {C : Cat} (a b : Ob C) : TYPE ≔ El (Mph' C a b);
symbol Id {C : Cat} (a : Ob C) : Mph a a;
symbol Comp {C : Cat} {a b c : Ob C} : Mph b c → Mph a b → Mph a c;

symbol ∘ {C : Cat} {a b c : Ob C} (f : Mph b c) (g : Mph a b) : Mph a c ≔ Comp f g;
notation ∘ infix left 6;

rule Comp (Id _) $g ↪ $g
with Comp $f (Id _) ↪ $f
with Comp $f (Comp $g $h) ↪ Comp (Comp $f $g) $h;
