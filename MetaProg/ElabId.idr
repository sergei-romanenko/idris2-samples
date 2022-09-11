module ElabId

import Language.Reflection
import Language.Reflection.Syntax
import Language.Reflection.Pretty

%language ElabReflection

%default total

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

mkNat25 : Nat
mkNat25 = %runElab (pure 25)

-- pw

pwElab : Nat -> Elab (Nat -> Nat)
pwElab Z = pure (const 1)
pwElab (S k) = do
  powerk <- pwElab k
  pure (\x => mult (powerk x) x)

%macro
pw : Nat -> Elab (Nat -> Nat)
pw n = pwElab n

cube : Nat -> Nat
cube = pw 3
