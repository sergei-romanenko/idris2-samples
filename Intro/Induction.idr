module Induction

import Syntax.PreorderReasoning
import Data.Nat

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
odd_1 = O1 E0

even_2 : Even 2
even_2 = E1 (O1 E0)

-- Uninhabited...

implementation Uninhabited (Odd Z) where
  uninhabited (O1 _) impossible

-- Inversion.

not_odd_Z : Odd Z -> Void
--not_odd_Z (O1 _) impossible
not_odd_Z odd_Z = absurd odd_Z

even_pred : Even (S n) -> Odd n
even_pred (E1 odd_n) = odd_n

odd_pred : Odd (S n) -> Even n
odd_pred (O1 even_n) = even_n

mutual
  %hint
  even_even : Even m -> Even n -> Even (m + n)
  even_even {m = Z} E0 even_n = the (Even n) even_n
  even_even {m = S m'} (E1 odd_m') even_n =
    -- E1 (odd_even odd_m' even_n)
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
    --O1 (even_even em' en)
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
dbl_injective' Z Z Refl = the (Z = Z) Refl
-- dbl_injective' 0 (S _) Refl impossible
-- dbl_injective' (S _) Z Refl impossible
dbl_injective' (S m') (S n') h =
  the (S m' = S n')
    $ cong S $
  the (m' = n')
    $ dbl_injective' m' n' $ 
  the (dbl m' = dbl n')
    $ cong (pred . pred) $
  the (S (S (dbl m')) = S (S (dbl n')))
    $ h
