module Intro.InfiniteDescent

{--
  Based on

    James Brotherston. Sequent Calculus Proof Systems for Inductive Definitions.
    PhD thesis, University of Edinburgh, 2006.
    http://hdl.handle.net/1842/1458
--}

import Data.Nat
import Data.Either
import Syntax.PreorderReasoning
import Control.Category
import Control.WellFounded


%default total

-- ==========

-- Implication reasoning

prefix 1  |~~
infixl 0  ~~>
infix  1  ...

-- Implication is a preorder relation...

public export
(|~~) : (0 a : Type) -> (a -> a)
(|~~) a = id

public export
(~~>) : (p : a -> b) -> (q : b -> c) -> (a -> c)
(~~>) p q = q . p

public export
(...) : (0 b : Type) -> (a -> b) -> (a -> b)
(...) b xy = xy

-- ==========


-- Mathematical induction.
-- Augustus de Morgan (1838).

indNat : {P : Nat -> Type} ->
  (p0 : P Z) -> (step : (m : Nat) -> P m -> P (S m)) ->
  (n : Nat) -> P n
indNat p0 step Z =
  p0
indNat p0 step (S k) =
  step k (indNat p0 step k)


-- Infinite descent.
-- Pierre de Fermat (1659)

descNat : {P : Nat -> Type} ->
  (np0 : P Z -> Void) -> (down : (m : Nat) -> P (S m) -> P m) ->
  (n : Nat) -> P n -> Void
descNat np0 down Z p0 =
  np0 p0
descNat np0 down (S k) p_sk =
  descNat np0 down k (down k p_sk)

-- S is injective.

namespace S_Injective

  s_inj : S m = S n -> m = n
  s_inj Refl = Refl

  s_inj' : S m = S n -> m = n
  s_inj' = \Refl => Refl

  s_inj'' : {m, n : Nat} -> S m = S n -> m = n
  s_inj'' = injective -- defined in Data.Nat

-- n : Nat is either `Z` or `S k`

caseNat : (n : Nat) -> (n = Z) `Either` (k ** n = S k)
caseNat Z = Left Refl
caseNat (S k) = Right (k ** Refl)


-- Not (Z = S n)

namespace NE_Z_S

  ne_z_s : (n : Nat) -> Z = S n -> Void
  ne_z_s _ Refl impossible

  ne_z_s' : (n : Nat) -> Z = S n -> Void
  ne_z_s' n z__sn =  absurd z__sn  -- defined in Data.Nat

namespace Plus_n_Z_1

  P : Nat -> Type
  P n = n + 0 = n

  base : P 0
  base = Refl

  step : (n : Nat) -> P n -> P (S n)
  step n p_n = cong S p_n

  plus_n_Z : (n : Nat) -> P n
  plus_n_Z = indNat base step

namespace Plus_n_Z_2

  plus_rz : (n : Nat) -> n + 0 = n
  plus_rz 0 =
    the (0 + 0 = 0) $
      Refl
  plus_rz (S k) =
    the (S k + Z = S k) $
      id $
    the (S (k + Z) = S k) $
      cong S $
    the (k + 0 = k) $
      plus_rz k

namespace Plus_n_Z_3

  plus_rz : (n : Nat) -> n + 0 = n
  plus_rz 0 = Calc $
    |~ 0 + 0
    ~~ 0     ... Refl
  plus_rz (S k) = Calc $
    |~ S k + 0
    ~~ S (k + 0) ... Refl
    ~~ S k       ... ( cong S (plus_rz k) )

namespace NEQ_n_Sn_1

  P : Nat -> Type
  P n = n = S n

  np0 : P Z -> Void
  np0 z__sz = absurd z__sz

  down : (n : Nat) -> P (S n) -> P n
  down n =
    |~~ (S n = S (S n))
    ~~> (n = S n)       ... ( injective )
  
  neq_n_Sn : (n : Nat) -> P n -> Void
  neq_n_Sn = descNat np0 down

namespace NEQ_n_Sn_2

  neq_n_Sn : (n : Nat) -> n = S n -> Void
  neq_n_Sn Z z__sz = absurd z__sz
  neq_n_Sn (S k) sk__ssk =
    neq_n_Sn k (injective sk__ssk)

namespace PrimNat

  -- `indNat` has the same structure as `primNat`.

  primNat : (base : Nat) -> (step : Nat -> Nat -> Nat) -> (n : Nat) -> Nat
  primNat base step Z =
    base
  primNat base step (S k) =
    step k (primNat base step k)

  -- `foldNat` is a special case of `primNat`.

  foldNat : (base : Nat) -> (step : Nat -> Nat) -> (n : Nat) -> Nat
  foldNat base step Z =
    base
  foldNat base step (S k) =
    step (foldNat base step k)

  double : (n : Nat) -> Nat
  double = foldNat Z (S . S)

  test_double : double 3  = 6
  test_double = Refl 

mutual

  data Even : Nat -> Type where
    Even0 : Even Z
    Even1 : Odd n -> Even (S n)

  data Odd : Nat -> Type where
    Odd1 : Even n -> Odd (S n)


odd_1 : Odd 1
odd_1 = Odd1 Even0

even_2 : Even 2
even_2 = Even1 (Odd1 Even0)


-- Inversion.

Uninhabited (Odd Z) where
  uninhabited (Odd1 _) impossible

%hint
even_S : {n : Nat} -> Even (S n) -> Odd n
even_S (Even1 odd_n) = odd_n

%hint
odd_S : {n : Nat} -> Odd (S n) -> Even n
odd_S (Odd1 even_n) = even_n


namespace Even_dbl_1

  -- "Ordinary" induction.

  even_dbl : (n : Nat) -> Even (n + n)
  even_dbl Z = Even0
  even_dbl (S k) =
    the (Even (S k + S k)) $
      id $
    the (Even (S (k + S k))) $
      rewrite sym $ plusSuccRightSucc k k in
      -- (\h => replace {p = Even . S}  (sym $ plusSuccRightSucc k k) h) $
    the (Even (S (S (k + k)))) $
      (Even1 . Odd1) $
    the (Even (k + k)) $
      even_dbl k

namespace Even_dbl_2

  -- "Ordinary" induction.

  even_dbl : (n : Nat) -> Even (n + n)
  even_dbl 0 = Even0
  even_dbl (S k) = (
    |~~ Even (k + k)
    ~~> Even (S (S (k + k))) ... (Even1 . Odd1)
    ~~> Even (S (k + S k))
      ... (\h => rewrite sym $ plusSuccRightSucc k k in h)
      -- ... (\h => replace {p = Even . S } (plusSuccRightSucc k k) h)
    ~~> Even (S k + S k)     ... id
    ) $ even_dbl k

namespace Odd_dbl_1

  -- "Infinite descent" in style of Fermat.

  not_odd_dbl : (n : Nat) -> Odd (n + n) -> Void
  not_odd_dbl 0 odd_0 = absurd odd_0
  not_odd_dbl (S k) odd_dbl_sk = not_odd_dbl k $
    the (Odd (k + k)) $
      even_S $
    the (Even (S (k + k))) $
      odd_S $
    the (Odd (S (S (k + k)))) $
      rewrite (plusSuccRightSucc k k) in
    the (Odd (S (k + S k))) $
      id $
    the (Odd (S k + S k)) $
      odd_dbl_sk

namespace Odd_dbl_2

  -- "Infinite descent" in style of Fermat.

  not_odd_dbl : (n : Nat) -> Odd (n + n) -> Void
  not_odd_dbl 0 odd_0 = absurd odd_0
  not_odd_dbl (S k) odd_dbl_sk = not_odd_dbl k $ (
    |~~ Odd (S k + S k)
    ~~> Odd (S (k + S k))   ... id
    ~~> Odd (S (S (k + k))) ... (\h => rewrite plusSuccRightSucc k k in h)
    ~~> Odd (k + k)         ... (even_S . odd_S)
    ) $ odd_dbl_sk

namespace EitherEvenOdd_1

  even'odd : (n : Nat) -> Even n `Either` Odd n
  even'odd 0 = Left Even0
  even'odd (S 0) = Right $ Odd1 Even0
  even'odd (S (S k)) with (even'odd k)
    _ | Left even_k = Left  $ Even1 (Odd1 even_k)
    _ | Right odd_k = Right $ Odd1 (Even1 odd_k)


namespace EitherEvenOdd_2

  even'odd : (n : Nat) -> Even n `Either` Odd n
  even'odd 0 = Left Even0
  even'odd (S 0) = Right $ Odd1 Even0
  even'odd (S (S k)) =
    bimap (Even1 . Odd1) (Odd1 . Even1) $ even'odd k


namespace EitherEvenOdd_3

  mutual

    even'odd : (n : Nat) -> Even n `Either` Odd n
    even'odd 0 = Left Even0
    even'odd (S k) =
      bimap Even1 Odd1 $ odd'even k

    odd'even : (n : Nat) -> Odd n `Either` Even n
    odd'even 0 = Right Even0
    odd'even (S k) =
      bimap Odd1 Even1 $ even'odd k


namespace EitherEvenOdd_4

  even'odd : (n : Nat) -> Even n `Either` Odd n
  even'odd 0 = Left Even0
  even'odd (S k) =
    mirror $ bimap Odd1 Even1 $ even'odd k


namespace EitherEvenOdd_5

  even'odd : (n : Nat) -> Even n `Either` Odd n
  even'odd =
    indNat (Left Even0) (\m => mirror . bimap Odd1 Even1)


namespace Even_Odd_1

  -- "Infinite descent" in style of Fermat.

  not_even_odd : (m : Nat) -> (Even m, Odd m) -> Void
  not_even_odd 0 (even_0 , odd_0) =
    absurd odd_0
  not_even_odd (S k) (even_sk , odd_sk) =
    not_even_odd k (odd_S odd_sk, even_S even_sk)


namespace Even_Odd_2

  -- A more Idris-idiomatic style...

  not_even_odd : (m : Nat) -> Even m -> Odd m -> Void
  not_even_odd 0 Even0 (Odd1 _) impossible
  not_even_odd (S k) (Even1 odd_k) (Odd1 even_k) =
    not_even_odd k even_k odd_k


-- The R example

namespace R_example

  data R : (x, y : Nat) -> Type where
    ZY : {y : Nat} -> R Z y
    XZ : {x : Nat} -> R x Z
    SS : {x, y : Nat} -> R (S (S x)) y -> R (S x) (S y)

  all_r : (x, y : Nat) -> R x y
  all_r x Z = XZ
  all_r Z (S y) = ZY
  all_r (S x) (S y) =
    SS (all_r (S (S x)) y)


-- The P & Q example

namespace P_and_Q_example

  mutual

    data P : (x : Nat) -> Type where
      PZ : P Z
      PS : {x : Nat} -> P x -> Q x (S x) -> P (S x)

    data Q : (x, y : Nat) -> Type where
      QZ : {x : Nat} -> Q x Z
      QS : {x, y : Nat} -> P x -> Q x y -> Q x (S y)

  mutual

    all_q : (x, y : Nat) -> Q x y
    all_q x Z = QZ
    all_q x (S y) =
      QS (all_p x) (all_q x y)

    all_p : (x : Nat) -> P x
    all_p Z = PZ
    all_p (S x) =
      PS (all_p x) (all_q x (S x))


-- The N' example

namespace N'_example

  data N' : (x, y : Nat) -> Type where
    NZ : {y : Nat} -> N' Z y
    NS : {x, y : Nat} -> N' y x -> N' (S x) y

  mutual

    all_n : (x, y : Nat) -> N' x y
    all_n Z y = NZ
    all_n (S x) y = NS (all_n y x)


-- The "problem" with Idris is that it is a statically-typed language,
-- while Brotherston deals with an untyped language.
-- Thus some examples are too easy to reproduce in Idris.
-- Hence, let us define natural numbers in "unnatural" way,
-- in order that they be a subset of an Idris type.


data BN : (bs : List Bool) -> Type where
  Z : BN []
  S  : BN bs -> BN (True :: bs)

bn3 : BN (True :: True :: True :: [])
bn3 = S (S (S Z))

mutual

  data BE : (bs : List Bool) -> Type where
    BE0 : BE []
    BE1 : BO bs -> BE (True :: bs)

  data BO : (bs : List Bool) -> Type where
    BO1 : BE bs -> BO (True :: bs)

be2 : BE (True :: True :: [])
be2 = BE1 (BO1 BE0)

bo3 : BO (True :: True :: True :: [])
bo3 = BO1 (BE1 (BO1 BE0))


namespace BE'BO_1

  be'bo : (bn : BN n) -> BE n `Either` BO n
  be'bo Z = Left BE0
  be'bo (S Z) = Right $ BO1 BE0
  be'bo (S (S bn)) =
    bimap (BE1 . BO1) (BO1 . BE1) $ be'bo bn


namespace BE'BO_2

  mutual

    be'bo : (bn : BN n) -> BE n `Either` BO n
    be'bo Z = Left BE0
    be'bo (S bn) =
      bimap BE1 BO1 $ bo'be bn

    bo'be : (bn : BN n) -> BO n `Either` BE n
    bo'be Z = Right BE0
    bo'be (S bn) =
      bimap BO1 BE1 $ be'bo bn

namespace BE'BO_3

  be'bo : (bn : BN n) -> BE n `Either` BO n
  be'bo Z = Left BE0
  be'bo (S bn) =
    mirror $ bimap BO1 BE1 $ be'bo bn


namespace BE'BO_BN_1

  be_bn : (be : BE n) -> BN n
  be_bn BE0 = Z
  be_bn (BE1 (BO1 be)) = S (S (be_bn be))

  be'bo_bn : (beo : BE n `Either` BO n) -> BN n
  be'bo_bn (Left be) = be_bn be
  be'bo_bn (Right (BO1 be)) = S (be_bn be)


namespace BE'BO_BN_2

  mutual

    be_bn : (be : BE n) -> BN n
    be_bn BE0 = Z
    be_bn (BE1 bo) = S (bo_bn bo)

    bo_bn : (bo : BO n) -> BN n
    bo_bn (BO1 be) = S (be_bn be)

  be'bo_bn : (beo : BE n `Either` BO n) -> BN n
  be'bo_bn = either be_bn bo_bn


-- Complete induction

indNatC' : {P : Nat -> Type} ->
  (step : (n : Nat) -> ((m : Nat) -> m `LT` n -> P m) -> P n) ->
  (n : Nat) -> Accessible LT n -> P n 
indNatC' step n (Access rec) =
  step n (\m, m_le_n => indNatC' step m  (rec m m_le_n))

indNatC : {P : Nat -> Type} ->
  (step : (n : Nat) -> ((m : Nat) -> m `LT` n -> P m) -> P n) ->
  (n : Nat) -> P n 
indNatC step n =
  indNatC' step n (sizeAccessible n)
