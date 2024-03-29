module Functors.EvalApplicative

%default total

----

data Expr
  = Var String
  | Val Int
  | Add Expr Expr

Env : Type
Env = List (String, Int)

data Eval : Type -> Type where
  MkEval : (Env -> Maybe a) -> Eval a

implementation Functor Eval where
  map f (MkEval g) = MkEval $ map f . g

implementation Applicative Eval where
  pure x = MkEval $ const (Just x)
  (MkEval f) <*> (MkEval g) = MkEval $ \e => f e <*> g e

fetch : String -> Eval Int
fetch x = MkEval fetchVal where
 fetchVal : Env -> Maybe Int
 fetchVal [] = Nothing
 fetchVal ((y, v) :: xs) =
    if x == y then (Just v) else (fetchVal xs)

eval : Expr -> Eval Int
eval (Var x) = fetch x
eval (Val i) = [| i |]  -- pure i
eval (Add e1 e2) = [| eval e1 + eval e2 |]
  -- (+) <$> eval e1 <*> eval e2

runEval : Expr -> Env -> Maybe Int
runEval e env = case eval e of
    MkEval f => f env

----

Env1 : Env
Env1 = [("x", 2), ("y", 3)]

run1 : runEval (Add (Var "y") (Val 7)) Env1 = Just 10
run1 = Refl

run2 : runEval (Var "z") Env1 = Nothing
run2 = Refl
