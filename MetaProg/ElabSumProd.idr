module ElabSumProd

import Language.Reflection
-- import Language.Reflection.Syntax
-- import Language.Reflection.Pretty

%language ElabReflection

%default total

mkProof : (g : TTImp) -> Elab TTImp
mkProof `(Builtin.Unit) =
  pure `(Builtin.MkUnit)
mkProof `(Prelude.Types.Nat) =
  pure `(0)
mkProof `(Builtin.Pair ~(a) ~(b)) = do
  p <- mkProof a
  q <- mkProof b
  pure $ `(MkPair ~(p) ~(q))
mkProof `(Prelude.Types.Either ~(a) ~(b)) = do
  left a <|> right b
  where
  left : TTImp -> Elab TTImp
  left a = do
    p <- mkProof a
    pure $ `(Left ~(p))
  right : TTImp -> Elab TTImp
  right b = do
    q <- mkProof b
    pure $ `(Right ~(q))
mkProof g = fail "I don't know how to prove this \{show g}"

autoSumProd : Elab ty
autoSumProd = do
  Just g <- goal
      | Nothing => fail "No goal to solve"
  p <- mkProof g
  check p

testUnit : ()
testUnit = %runElab autoSumProd

testNat : Nat
testNat = %runElab autoSumProd

testPUU : ((), ())
testPUU = %runElab autoSumProd

testEUV : Either () Void
testEUV = %runElab autoSumProd

testEVU : Either Void ()
testEVU = %runElab autoSumProd

testEVEVU : Either Void (Either Void ())
testEVEVU = %runElab autoSumProd

-- testEVEVV : Either Void (Either Void Void)
-- testEVEVV = %runElab autoSumProd
