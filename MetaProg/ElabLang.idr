module ElabLang

import Data.Fin
import Data.Vect
import Language.Reflection
import Language.Reflection.Syntax
-- import Language.Reflection.Pretty

%language ElabReflection

-- Lang

data Lang : Nat -> Type where
  V    : (i : Fin n) -> Lang n
  Ap   : (e1, e2 : Lang n) -> Lang n
  Lam  : (e : Lang (S n)) -> Lang n
  CstI : (x : Int) -> Lang n
  FFI  : (name : Name) -> Lang n

exampleFun : Lang 0
exampleFun = Lam $ Lam $
  Ap (Ap (FFI `{(+)}) (V 0)) (V 1)

exampleExpr : Lang 0
exampleExpr = Ap (Ap exampleFun (CstI 10)) (CstI 20)

-- mkLang

mkLang : (ctxt : Vect k Name) -> (lang : Lang k) -> Elab TTImp
mkLang ctxt (V i) = do
  let n = index i ctxt
  -- IVar EmptyFC n
  pure $ var n
mkLang ctxt (Ap e1 e2) = do
  t1 <- mkLang ctxt e1
  t2 <- mkLang ctxt e2
  -- pure $ IApp EmptyFC t1 t2
  pure $ t1 .$ t2
mkLang ctxt (Lam e) = do
  n <- genSym "argument"
  body <- mkLang (n :: ctxt) e
  -- pure $ ILam EmptyFC MW ExplicitArg (Just n) (Implicit EmptyFC False) body
  pure $ lambdaArg n .=> body
mkLang ctxt (CstI x) =
  -- pure $ IPrimVal EmptyFC (I x)
  pure $ primVal (I x)
mkLang ctxt (FFI name) =
  -- IVar EmptyFC n
  pure $ var name

-- elabLang

elabLang : Lang 0 -> Elab ty
elabLang e = do
  c <- mkLang [] e
  check c

-- Tests

compiledFun : Int -> Int -> Int
compiledFun = %runElab (elabLang exampleFun)

compiled_2_3 : compiledFun 2 3 = 5
compiled_2_3 = Refl

compiledExpr : Int
compiledExpr = %runElab (elabLang exampleExpr)

compiledExprTest : ElabLang.compiledExpr = 30
compiledExprTest = Refl
