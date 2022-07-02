module Hoeck.SigmaTypes1

import Data.So
import Data.Vect
import Data.DPair
import Data.Singleton


takeWhile : (a -> Bool) -> Vect m a -> (n ** Vect n a)
takeWhile f [] = (0 ** [])
takeWhile f (x :: xs) with (f x)
  _ | False = (0 ** [])
  _ | True with (takeWhile f xs)
    _ | (n ** ys) = (1 + n ** x :: ys)

test_Z_eq_Z : So $ Z == Z
test_Z_eq_Z = Oh

test_takeWhile : (takeWhile (== 1) [1, 1, 1, 2, 3]) = (3 ** [1, 1, 1])
test_takeWhile = Refl

test_takeWhile0 : takeWhile (== 1) [] = (0 ** [])
test_takeWhile0 = Refl

takeWhileExists : (a -> Bool) -> Vect m a -> Exists (\n => Vect n a)
takeWhileExists f [] = Evidence 0 []
takeWhileExists f (x :: xs) with (f x)
  _ | False = Evidence 0 []
  _ | True with (takeWhileExists f xs)
    _ | Evidence n ys = Evidence (1 + n) (x :: ys)

test_takeWhileExists : (takeWhileExists (== 1) [1, 1, 1, 2, 3]) = (Evidence 3 [1, 1, 1])
test_takeWhileExists = Refl

vectLength : Vect n a -> Singleton n
vectLength [] = Val 0
vectLength (x :: xs) with (vectLength xs)
  vectLength (x :: xs) | Val n' = Val (S n')

valInjective : Singleton x = Singleton y -> x = y
valInjective Refl = Refl

exVal : Singleton x -> (y ** x = y)
exVal (Val _) = (x ** Refl)

test_exVal : fst (exVal(Val 5)) = 5
test_exVal = Refl

filterVect : (f : a -> Bool) -> Vect m a -> (n ** Vect n a)
filterVect f [] = (0 ** [])
filterVect f (x :: xs) with (filterVect f xs)
  _ | (m' ** xs') with (f x)
    _ | False = (m' ** xs')
    _ | True = (1 + m' ** x :: xs')

mapVectMaybe : (f : a -> Maybe b) -> Vect m a -> (n ** Vect n b)
mapVectMaybe f [] = (0 ** [])
mapVectMaybe f (x :: xs) with (mapVectMaybe f xs)
  _ | (m' ** ys') with (f x)
      _ | Nothing = (m' ** ys')
      _ | (Just y) = (1 + m' ** y :: ys')
  
%hint
dropVectWhileEx : (p : a -> Bool) -> (xs : Vect m a) -> Exists (\n => Vect n a)
dropVectWhileEx p [] = Evidence 0 []
dropVectWhileEx {m = 1 + m'} p (x :: xs) with (p x)
  _ | False = Evidence (1 + m') (x :: xs)
  _ | True = dropVectWhileEx p xs

dropVectWhile : (p : a -> Bool) -> (xs : Vect m a) -> (n ** Vect n a)
dropVectWhile p xs with (dropVectWhileEx p xs)
  _ | (Evidence m' xs') with (vectLength xs')
    _ | (Val m') = (m' ** xs')
