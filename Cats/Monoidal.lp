
require open Cats.Universe;
require open Cats.Cat;
require open Cats.Functor;
require open Cats.Product;

// Codes for strict monoidal categories
constant symbol SMonCat' : U;
symbol SMonCat : TYPE ≔ El SMonCat';
symbol SMCat' : SMonCat → Cat;
symbol SMCat (C : SMonCat) : TYPE ≔ Ob (SMCat' C);

// Monoidal product and neutral
symbol sProd (C : SMonCat) : Funct (PCat' (SMCat' C) (SMCat' C)) (SMCat' C);
symbol sUnit (C : SMonCat) : SMCat C;

// Associativity and unitality
rule Fob (sProd $C) (mkP $x (Fob (sProd _) (mkP $y $z))) ↪ Fob (sProd $C) (mkP (Fob (sProd $C) (mkP $x $y)) $z)
with Fob (sProd _) (mkP (sUnit _) $x) ↪ $x
with Fob (sProd _) (mkP $x (sUnit _)) ↪ $x;
rule Fmph (sProd $C) (mkPf $f (Fmph (sProd $C) (mkPf $g $h))) ↪ Fmph (sProd $C) (mkPf (Fmph (sProd $C) (mkPf $f $g)) $h)
with Fmph (sProd _) (mkPf (Id (sUnit _)) $f) ↪ $f
with Fmph (sProd _) (mkPf $f (Id (sUnit _))) ↪ $f;
