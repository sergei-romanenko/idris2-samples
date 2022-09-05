module ElabId

import Language.Reflection
import Language.Reflection.Syntax
import Language.Reflection.Pretty

%language ElabReflection

mkIdFn : TTImp
mkIdFn = `(\x => x)

mkIdFnNat : Nat -> Nat
mkIdFnNat = %runElab (check mkIdFn)

mkId : Elab (a -> a)
mkId = pure (\x => x)

%macro
mkIdMacro : Elab (a -> a)
mkIdMacro = pure (\x => x)

idNat : Nat -> Nat
idNat = %runElab mkId

-- :printdef idNat
-- idNat 25

idNat' : Nat -> Nat
idNat' = mkIdMacro

idUnit : () -> ()
idUnit = %runElab mkId

idString : String -> String
idString = %runElab mkId

idBool : Bool -> Bool
idBool = %runElab mkId

idNat1 : Nat -> Nat
idNat1 = %runElab (do x <- genSym "x"; pure (\x => x))

mkNat25 : Nat
mkNat25 = %runElab (pure (the Nat 25))
