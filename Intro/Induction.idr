module Intro.Induction

import Syntax.PreorderReasoning
import Data.Nat
import Data.List

import Intro.ImpReasoning

%default total

--
-- Now, let's prove something by means of preorder reasoning.
--

mutual

  data Even : Nat -> Type where
    E0 : Even Z
    E1 : Odd n -> Even (S n)

  data Odd : Nat -> Type where
    O1 : Even n -> Odd (S n)

odd_1 : Odd 1
odd_1 =
  the (Odd 1)   $ O1 $
  the (Even 0)  $ E0

even_2 : Even 2
even_2 =
  the (Even 2)  $ E1 $
  the (Odd 1)   $ O1 $
  the (Even 0)  $ E0

-- Uninhabited...

implementation Uninhabited (Odd Z) where
  uninhabited (O1 _) impossible

-- Negation

not_odd_Z : Odd Z -> Void
not_odd_Z (O1 _) impossible

not_odd_Z' : Odd Z -> Void
not_odd_Z' odd_Z = absurd odd_Z

-- Inversion.

even_pred : Even (S n) -> Odd n
even_pred (E1 odd_n) = odd_n

odd_pred : Odd (S n) -> Even n
odd_pred (O1 even_n) = even_n

mutual

  %hint
  even_even : Even m -> Even n -> Even (m + n)
  even_even {m = Z} E0 even_n =
    the (Even n) $ even_n
  even_even {m = S m'} (E1 odd_m') even_n =
    the (Even (S m' + n))
      $ id $
    the (Even (S (m' + n)))
      $ E1 $
    the (Odd (m' + n))
      $ odd_even
        (the (Odd m') $ odd_m')
        (the (Even n) $ even_n)

  %hint
  odd_even : Odd m -> Even n -> Odd (m + n)
  -- odd_even {m = Z} om en impossible
  odd_even {m = (S m')} (O1 em') en =
    the (Odd (S m' + n))
      $ id $
    the (Odd (S (m' + n)))
      $ O1 $
    the (Even (m' + n)) 
      $ even_even
        (the (Even m') $ em')
        (the (Even n) $ en)

--
-- Injectivity of `dbl`.
--

dbl : Nat -> Nat
dbl Z = Z
dbl (S n) = S (S (dbl n))

-- "Correctness"

dbl_correct : (n : Nat) -> dbl n = n + n
dbl_correct 0 = Refl
dbl_correct (S n') = Calc $
  |~ dbl (S n')
  ~~ S (S (dbl n'))   ...( Refl )
  ~~ S (S (n' + n'))  ...( cong (S . S) (dbl_correct n') )
  ~~ S (n' + S n')    ...( cong S (plusSuccRightSucc n' n') )
  ~~ S n' + S n'      ...( Refl )

-- Now let us prove this:

dbl_injective : (m, n : Nat) -> dbl m = dbl n -> m = n
dbl_injective Z Z Refl = Refl
-- dbl_injective Z (S _) Refl impossible
-- dbl_injective (S _) Z Refl impossible
dbl_injective (S m') (S n') h =
  -- This is short, but looks like a mystery.
  (cong S . dbl_injective m' n' . cong (pred . pred)) h


-- Let us try to rewrite the above proof in a more "human-friendly" form
-- by using `the` and `$`.

dbl_injective' : (m, n : Nat) -> dbl m = dbl n -> m = n
dbl_injective' Z Z Refl =
  the (dbl Z = dbl Z)
    $ id $
  the (Z = Z)
    $ Refl
dbl_injective' (S m') (S n') h =
  the (S m' = S n')
    $ cong S $
  the (m' = n')
    $ dbl_injective' m' n' $ 
  the (dbl m' = dbl n')
    $ cong (pred . pred) $
  the (S (S (dbl m')) = S (S (dbl n')))
    $ id $
  the (dbl (S m') = dbl (S n'))
    $ h

dbl_injective'' : (m, n : Nat) -> dbl m = dbl n -> m = n
dbl_injective'' Z Z =
  |~~ (dbl Z = dbl Z) ~~> (Z = Z) ...( id )
dbl_injective'' Z (S n') = absurd
dbl_injective'' (S m') 0 = absurd
dbl_injective'' (S m') (S n') =
  |~~ (dbl (S m') = dbl (S n'))
  ~~> (S (S (dbl m')) = S (S (dbl n')))  ...( id )
  ~~> (dbl m' = dbl n')                  ...( cong (pred . pred) )
  ~~> (m' = n')                          ...( dbl_injective'' m' n' )
  ~~> (S m' = S n')                      ...( cong S )

-- A subtle point: without `{x}` we get the error
-- "Rewriting by length (replicate n' (Nat x n')) = n' did not change type"!

replicateToProperLength : (n : Nat) -> length (replicate n x) = n
replicateToProperLength Z = Refl
replicateToProperLength (S n') =
  rewrite replicateToProperLength {x} n' in
  Refl

-- Here we don't have to write `{x}`, because `x` appears in
--- `the (length (replicate n' x) = n')`.

replicateToProperLength' : (n : Nat) -> length (replicate n x) = n
replicateToProperLength' Z =
  the (Z = Z) $ Refl
replicateToProperLength' (S n') =
  rewrite the (length (replicate n' x) = n') 
    $ replicateToProperLength' n' in
  the (S n' = S n')
    $ Refl


namespace RevRev

  %hide Prelude.List.reverse
  %hide Prelude.Types.List.(++)

  (++) : (xs, ys : List a) -> List a
  [] ++ ys = ys
  (x :: xs) ++ ys = x :: xs ++ ys

  reverse : List a -> List a
  reverse [] = []
  reverse (x :: xs) = reverse xs ++ [x]

  test_reverse3 : reverse [1, 2, 3] = [3, 2, 1]
  test_reverse3 = Refl

  %hint
  appendNilRightNeutral : (xs : List a) -> xs ++ [] = xs
  appendNilRightNeutral [] = Calc $
    |~ [] ~~ [] ...( Refl )
  appendNilRightNeutral (x :: xs) = Calc $
    |~ (x :: xs) ++ []
    ~~ x :: xs
      ...( cong (x ::) $ appendNilRightNeutral xs )

  %hint
  appendAssociative :
    (xs, ys, zs : List a) -> xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
  appendAssociative [] ys zs = Refl
  appendAssociative (x :: xs) ys zs = Calc $
    |~ x :: (xs ++ (ys ++ zs))
    ~~ x :: ((xs ++ ys) ++ zs)
      ...( cong (x ::) (appendAssociative xs ys zs) )

  %hint
  reverseAppend : (xs : List a) -> (ys : List a) ->
    reverse (xs ++ ys) = reverse ys ++ reverse xs
  reverseAppend [] ys =
    sym $ appendNilRightNeutral(reverse ys)
  reverseAppend (x :: xs) ys = Calc $
    |~ (reverse (xs ++ ys) ++ [x])
    ~~ ((reverse ys ++ reverse xs) ++ [x])
      ...( cong (++ [x]) $ reverseAppend xs ys )
    ~~ (reverse ys ++ (reverse xs ++ [x]))
      ...( sym $ appendAssociative (reverse ys) (reverse xs) [x] )

  reverseReverse : (xs : List a) -> reverse (reverse xs) = xs
  reverseReverse [] = Refl
  reverseReverse (x :: xs) = Calc $
    |~ reverse (reverse xs ++ [x])
    ~~ (reverse [x] ++ reverse (reverse xs))
      ... ( reverseAppend (reverse xs) [x] )
    ~~ (x :: reverse (reverse xs))
      ... ( Refl )
    ~~ x :: xs
       ... ( cong (x ::) (reverseReverse xs) )
