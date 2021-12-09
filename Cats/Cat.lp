
require open Cats.Universe;

constant symbol Cat' : U;
symbol Cat : TYPE ≔ El Cat';
constant symbol Ob : Cat → TYPE;
constant symbol Mph' (C : Cat) : Ob C → Ob C → U;
symbol Mph {C : Cat} (a b : Ob C) : TYPE ≔ El (Mph' C a b);
constant symbol Id {C : Cat} (a : Ob C) : Mph a a;
symbol Comp {C : Cat} {a b c : Ob C} : Mph b c → Mph a b → Mph a c;

symbol ∘ {C : Cat} {a b c : Ob C} (f : Mph b c) (g : Mph a b) : Mph a c ≔ Comp f g;
notation ∘ infix left 6;

rule Comp (Id _) $g ↪ $g
with Comp $f (Id _) ↪ $f
with Comp $f (Comp $g $h) ↪ Comp (Comp $f $g) $h;
