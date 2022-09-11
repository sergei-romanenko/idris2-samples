module ElabMonoid

import Data.Nat
import Decidable.Equality
import Syntax.PreorderReasoning

import Language.Reflection

%language ElabReflection

%default total

----

interface IsMonoid a where
  neut : a
  op : a -> a -> a
  neutLeftId : (x : a) -> neut `op` x = x
  neutRightId : (x : a) -> x `op` neut = x
  assoc : (x, y, z : a) -> x `op` (y `op` z) = (x `op` y) `op` z

implementation IsMonoid () where
  neut = ()
  op () () = ()
  neutLeftId () = Refl
  neutRightId () = Refl
  assoc () () () = Refl

implementation [plusMonoid] IsMonoid Nat where
  neut = Z
  op = plus
  neutLeftId = plusZeroLeftNeutral
  neutRightId = plusZeroRightNeutral
  assoc = plusAssociative

implementation [multMonoid] IsMonoid Nat where
  neut = 1
  op = mult
  neutLeftId = multOneLeftNeutral
  neutRightId = multOneRightNeutral
  assoc = multAssociative

implementation IsMonoid (List a) where
  neut = []
  op = (++)
  neutLeftId _ = Refl
  neutRightId = appendNilRightNeutral
  assoc = appendAssociative

----

data MonoidExpr a =
  NEUT | LIT a | OP (MonoidExpr a) (MonoidExpr a)

interpExpr : IsMonoid a => MonoidExpr a -> a
interpExpr NEUT = neut
interpExpr (LIT v) = v
interpExpr (OP x y) = interpExpr x `op` interpExpr y

----

expr2 : (x, y : a) -> MonoidExpr a
expr2 x y = (OP (OP NEUT (LIT x)) (OP (LIT y) NEUT))

ie1 : interpExpr (expr2 () ()) = ()
ie1 = Refl

ie2 : interpExpr @{ElabMonoid.plusMonoid} (expr2 3 7) = 10
ie2 = Refl

ie3 : interpExpr @{ElabMonoid.multMonoid} (expr2 3 7) = 21
ie3 = Refl

----

interpList : IsMonoid a => List a -> a
interpList xs = foldr op neut xs

flattenExpr : MonoidExpr a -> List a
flattenExpr NEUT = []
flattenExpr (LIT x) = [x]
flattenExpr (OP x y) = flattenExpr x ++ flattenExpr y

%hint
opAppend : IsMonoid a => (xs, ys : List a) ->
  interpList xs `op` interpList ys = interpList (xs ++ ys)
opAppend [] ys = Calc $
  |~ (interpList [] `op` interpList ys)
  ~~ (neut `op` interpList ys)
    ... Refl
  ~~ interpList ys
    ... (neutLeftId (interpList ys))
  ~~ interpList ([] ++ ys)
    ... Refl
opAppend (x :: xs) ys = Calc $
  |~ (interpList (x :: xs) `op` interpList ys)
  ~~ ((x `op` interpList xs) `op` interpList ys)
    ... Refl
  ~~ (x `op` (interpList xs `op` interpList ys))
    ... (sym $ (assoc x (interpList xs) (interpList ys)))
  ~~ (x `op` interpList (xs ++ ys))
    ... (cong (op x) (opAppend xs ys))
  ~~ interpList (x :: (xs ++ ys))
    ... Refl
  ~~ interpList ((x :: xs) ++ ys)
    ... Refl

-- `flatten` and `interpList` are correct wrt `interpExpr`

%hint
flattenOk : IsMonoid a => (e : MonoidExpr a) ->
  interpExpr e = interpList (flattenExpr e)
flattenOk NEUT = Refl
flattenOk (LIT v) = Calc $
  |~ interpExpr (LIT v)
  ~~ v
    ... Refl
  ~~ op v neut
    ... (sym $ neutRightId v)
  ~~ interpList (flattenExpr (LIT v))
    ... Refl
flattenOk (OP x y) = Calc $
  |~ interpExpr (OP x y)
  ~~ (interpExpr x `op` interpExpr y)
    ... Refl
  ~~ (interpList (flattenExpr x) `op` interpList (flattenExpr y))
    ... (cong2 op (flattenOk x) (flattenOk y))
  ~~ interpList (flattenExpr x ++ flattenExpr y)
    ... (opAppend (flattenExpr x) (flattenExpr y))
  ~~ interpList (flattenExpr (OP x y))
    ... Refl

monoidReflection : IsMonoid a => (x, y : MonoidExpr a) ->
  interpList (flattenExpr x) = interpList (flattenExpr y) ->
  interpExpr x = interpExpr y
monoidReflection x y h = Calc $
  |~ interpExpr x
  ~~ interpList (flattenExpr x)
    ... (flattenOk x)
  ~~ interpList (flattenExpr y)
    ... h
  ~~ interpExpr y
    ... (sym $ flattenOk y)

monoidReflection2 : IsMonoid a => (x, y : MonoidExpr a) ->
  flattenExpr x = flattenExpr y ->
  interpExpr x = interpExpr y
monoidReflection2 x y h = Calc $
  |~ interpExpr x
  ~~ interpList (flattenExpr x)
    ... (flattenOk x)
  ~~ interpList (flattenExpr y)
    ... (cong interpList h)
  ~~ interpExpr y
    ... (sym $ flattenOk y)

--  Reification of monoid expressions to the custom expression type.

reifyExpr : IsMonoid a => TTImp -> Elab (MonoidExpr a)
reifyExpr `(neut) = do
  pure NEUT
reifyExpr `(op ~x ~y) = do
  mx <- reifyExpr x
  my <- reifyExpr y
  pure (OP mx my)
reifyExpr v = do
  mv <- check v
  pure (LIT mv)

testReifyExprElab : MonoidExpr Nat
testReifyExprElab = %runElab reifyExpr @{plusMonoid} `(op 10 20)

-- A tactic for simplifying equalities of monoid expressions using reflection.

{-
partial
asMonoid : (dict : Raw) -> Elab ()
asMonoid dict =
  case !goalType of
    `((=) {A=~A} {B=~B} ~e1 ~e2) =>
      do l <- gensym "L"
         r <- gensym "R"

         remember l `(MonoidExpr ~A); reifyExpr e1
         remember r `(MonoidExpr ~B); reifyExpr e2

         equiv `((=) {A=~A} {B=~B}
                     (interpExpr {a=~A} @{~dict} ~(Var l))
                     (interpExpr {a=~B} @{~dict} ~(Var r)))

         [h] <- apply `(monoidReflection {a=~A} @{~dict}
                                         ~(Var l) ~(Var r)) [True]
         solve
         focus h
-}

reifyEquation : IsMonoid a => TTImp -> Elab (MonoidExpr a, MonoidExpr a)
reifyEquation `(Equal ~x ~y) = do
  mx <- reifyExpr x
  my <- reifyExpr y
  pure (mx, my)
reifyEquation eq = fail "Unable to reify Equation"


partial
solveReflected : IsMonoid a => DecEq a => TTImp -> Elab (t)
solveReflected @{dict} `(Builtin.Equal ~(l) ~(r)) = do
  ml <- reifyExpr @{dict} l
  mr <- reifyExpr @{dict} r
  let el = interpExpr ml
  let er = interpExpr mr
  -- h : flattenExpr ml = flattenExpr mr
  let Yes ml_eq_mr = decEq (flattenExpr ml) (flattenExpr mr)
    | No _ => fail "Failed to prove this"
  let mrefl = monoidReflection2 @{dict} ml mr ml_eq_mr
  let Yes el_eq_er = decEq el er
    | No _ => fail "Not eq"
  pure $ ?solveReflected_rhs
  -- fail "Not done"
solveReflected g = do
  fail "The goal is not an equation"
  -- fail "I don't know how to prove this"

%macro
partial
prove : IsMonoid a => DecEq a => Elab (a = a)
prove @{dict} = do
  env <- localVars
  Just g <- goal
      | Nothing => fail "No goal to solve"
  solveReflected @{dict} g

----

{-
test1 : IsMonoid a => (w, x, y, z : a) ->
  (( w `op` x) `op` (y `op` z)) =
    (w `op` (x `op` (y `op` (z `op` neut {a=a}))))
test1 @{dict} w x y z =
  %runElab (do asMonoid (Var `{dict}); reflexivity)
-}
