module Sqrt2IsIrrational.Sqrt2

--   This has been produced by rewriting the Coq code by
--   Pierre Corbineau in
--     http://www-verimag.imag.fr/~corbinea/ftp/programs/sqrt2.v

--   There is no m and n such that
--     n /= 0 and m*m = 2 * (n*n)
--   Hence, sqrt 2 is irrational.

--
-- Informal proof
--
-- Suppose that m*m = 2 * (p*p). Then
--
--     2 * (p*p) is even -> m*m is even -> m is even.
--
-- Let m = 2 * n. Then
--
--     (2*n)*(2*n) = 2 * (p*p) ->
--     4*(n*n) = 2*(p*p) ->
--     2*(n*n) = p*p ->
--     p*p = 2*(n*n).
--
-- Compare
--      m * m = 2*(p * p) and
--      p * p = 2*(n * n) !
-- We come to the same equation, in which m has been replaced with p,
-- and p with n.
--
-- Doing the same once more, we come to the equation
--     n * n = 2*(q * q)
-- where m = 2*n and p = 2*q. Note that q = 0 iff p = 0!
--
-- We can repeat the above step several times, but, eventually, we come
-- to p = 0. Which contradicts the original assumption that p /= 0.

import Data.Nat
import Data.Either
import Control.WellFounded
import Syntax.PreorderReasoning
import Decidable.Equality

%default total

-- ==========

-- Implication reasoning

prefix 1  |~~
infixl 0  ~~>
infix  1  ...
infixr 0 |>

-- Implication is a preorder relation...

(|~~) : (0 a : Type) -> (a -> a)
(|~~) a = id

(~~>) : (p : a -> b) -> (q : b -> c) -> (a -> c)
(~~>) p q = q . p

(...) : (0 b : Type) -> (a -> b) -> (a -> b)
(...) b xy = xy

(|>) : forall a, b. (x : a) -> (f : a -> b) -> b
(|>) x f = f x

-- ==========

dbl : Nat -> Nat
dbl n = n + n

sq : Nat -> Nat
sq n = n * n

div2 : (n : Nat) -> Nat
div2 Z = Z
div2 (S Z) = Z
div2 (S (S n)) = S (div2 n)

%hint
dbl_S : (n : Nat) -> dbl (S n) = S (S (dbl n))
dbl_S n = Calc $
  |~ dbl (S n)
  ~~ S (n + S n)   ... Refl
  ~~ S (S (n + n)) ... (cong S $ sym $ plusSuccRightSucc n n)
  ~~ S (S (dbl n)) ... Refl

%hint
div2_dbl : (n : Nat) -> div2 (dbl n) = n
div2_dbl Z = Refl
div2_dbl (S n) = Calc $
  |~ div2(dbl (S n))
  ~~ div2 (S (S (dbl n))) ... (cong div2 (dbl_S n))
  ~~ S (div2 (dbl n))     ... Refl
  ~~ S n                  ... (cong S (div2_dbl n))

%hint
dbl_inj : dbl m = dbl n -> m = n
dbl_inj eq_2m_2n = Calc $
  |~ m
  ~~ div2 (dbl m) ... (sym $ div2_dbl m)
  ~~ div2 (dbl n) ... (cong div2 eq_2m_2n)
  ~~ n            ... (div2_dbl n)

%hint
dbl_mult_l : dbl (m * n) = m * (dbl n)
dbl_mult_l = Calc $
  |~ dbl (m * n)
  ~~ dbl (n * m)    ... (cong dbl $ multCommutative m n)
  ~~ n * m + n * m     ... Refl
  ~~ (n + n) * m       ... (sym $ multDistributesOverPlusLeft n n m)
  ~~ m * (n + n)       ... (multCommutative (n + n) m)
  ~~ m * (dbl n)    ... Refl

%hint
dbl_mult_r : dbl (m * n) = (dbl m) * n
dbl_mult_r = Calc $
  |~ dbl (m * n)
  ~~ dbl (n * m)    ... (cong dbl $ multCommutative m n)
  ~~ n * (dbl m)    ... (dbl_mult_l)
  ~~ (dbl m) * n    ... (multCommutative n (dbl m))

mutual

  data Even : Nat -> Type where
    Even0 : Even Z
    Even1 : Odd n -> Even (S n)

  data Odd : Nat -> Type where
    Odd1 : Even n -> Odd (S n)

Uninhabited (Odd Z) where
  uninhabited (Odd1 _) impossible

even'odd : (n : Nat) -> Even n `Either` Odd n
even'odd Z =
  Left Even0
even'odd (S n) =
  mirror $ bimap Odd1 Even1 (even'odd n)

%hint
even_dbl : (n : Nat) -> Even (dbl n)
even_dbl Z = Even0
even_dbl (S Z) = Even1 (Odd1 Even0)
even_dbl (S (S n)) = even_dbl n |>
  |~~ Even (dbl n)
  ~~> Even (S (S (dbl n)))     ... (Even1 . Odd1)
  ~~> Even (dbl (S n))         ... (\h => rewrite dbl_S n in h)
  ~~> Even (S (S (dbl (S n)))) ... (Even1 . Odd1)
  ~~> Even (dbl (S (S n)))     ... (\h => rewrite dbl_S (S n) in h)

%hint
even_dbl_div2 : Even n -> dbl (div2 n) = n
even_dbl_div2 Even0 = ?even_dbl_div2_rhs_0
even_dbl_div2 (Even1 (Odd1 {n = n} even_n)) = Calc $
  |~ dbl (div2 (S (S n)))
  ~~ dbl (S (div2 n))     ... Refl
  ~~ S (S (dbl (div2 n))) ... (dbl_S (div2 n))
  ~~ S (S n)              ... (cong (S . S) (even_dbl_div2 even_n))


%hint
even_even_plus : (m : Nat) -> Even m -> Even (m + n) -> Even n
even_even_plus 0 Even0 even_n = even_n
even_even_plus (S 0) (Even1 odd_Z) (Even1 odd_n) = absurd odd_Z
even_even_plus (S (S m)) (Even1 (Odd1 even_m)) (Even1 (Odd1 even_mn)) =
  even_even_plus m even_m even_mn


%hint
odd_even_mult : {m, n : Nat} -> Odd m -> Even (m * n) -> Even n
odd_even_mult (Odd1 Even0) =
  |~~ Even (1 * n)
  ~~> Even (n + 0) ... id
  ~~> Even n       ... (\h => rewrite sym $ plusZeroRightNeutral n in h)
odd_even_mult (Odd1 (Even1 {n=m} odd_m)) =
  |~~ Even (n + (n + m * n))
  ~~> Even ((n + n) + m * n)
    ... (\h => rewrite sym $ plusAssociative n n (m * n) in h)
  ~~> Even (m * n)  ... (even_even_plus (dbl n) (even_dbl n))
  ~~> Even n        ... (odd_even_mult odd_m)


%hint
even_sq : {n : Nat} -> Even (sq n) -> Even n
even_sq even_nn with (even'odd n)
  _ | Left even_n = even_n
  _ | Right odd_n = odd_even_mult odd_n even_nn

%hint
even_dd_sq_div2 : {n : Nat} -> Even n ->
  dbl (dbl (sq (div2 n))) = sq n
even_dd_sq_div2 even_n = Calc $
  |~ dbl (dbl (sq (div2 n)))
  ~~ dbl (dbl (div2 n * div2 n)) ... Refl
  ~~ dbl (div2 n * dbl (div2 n)) ... (cong dbl dbl_mult_l)
  ~~ dbl (div2 n) * dbl (div2 n) ... (dbl_mult_r)
  ~~ sq n 
    ... (cong2 (*) (even_dbl_div2 even_n) (even_dbl_div2 even_n))

-- ==========
-- The most sophisticated part:
--   NonZero m -> sq m = dbl (sq p) -> Void.
-- The proof is by reducing the problem to a "smaller" one:
--   NonZero (m/2) -> sq (m/2) = dbl (sq (p/2)) -> Void
-- ==========

-- descent_step

descent_step : (m, p :Nat) -> sq m = dbl (sq p) ->
  sq (div2 m) = dbl (sq (div2 p))
descent_step m p sq_m__d_sq_p =
  sq_n__d_sq_q
  where

  even_m : Even m
  even_m = even_dbl (sq p) |>
    |~~ Even (dbl (sq p))
    ~~> Even (sq m) ... (\h => rewrite sq_m__d_sq_p in h)
    ~~> Even m ... (even_sq)

  dd_sq_n__d_sq_p : dbl (dbl (sq (div2 m))) = dbl (sq p)
  dd_sq_n__d_sq_p = Calc $
    |~ dbl (dbl (sq (div2 m)))
    ~~ sq m       ... (even_dd_sq_div2 even_m)
    ~~ dbl (sq p) ... (sq_m__d_sq_p)

  d_sq_n__sq_p : dbl (sq (div2 m)) = sq p
  d_sq_n__sq_p = dbl_inj dd_sq_n__d_sq_p

  even_p : Even p
  even_p = even_dbl (sq (div2 m)) |>
    |~~ Even (dbl (sq (div2 m)))
    ~~> Even (sq p)  ... (\h => rewrite sym $ d_sq_n__sq_p in h)
    ~~> Even p       ... (even_sq)

  dd_sq_n__ddd_sq_q :
    dbl (dbl (sq (div2 m))) = dbl (dbl (dbl (sq (div2 p))))
  dd_sq_n__ddd_sq_q = Calc $
    |~ dbl (dbl (sq (div2 m)))
    ~~ dbl (sq p)
      ... ( dd_sq_n__d_sq_p )
    ~~ dbl (dbl (dbl (sq (div2 p))))
      ... ( cong dbl (sym $ even_dd_sq_div2 even_p) )

  sq_n__d_sq_q : sq (div2 m) = dbl (sq (div2 p))
  sq_n__d_sq_q = dbl_inj (dbl_inj dd_sq_n__ddd_sq_q)

-- descent

%hint
div2_lte : (n : Nat) -> div2 n `LTE`  n
div2_lte Z = LTEZero
div2_lte (S Z) = LTEZero
div2_lte (S (S n')) =
  LTESucc $ lteSuccRight $ div2_lte n'

%hint
div2_lt : (n : Nat) -> NonZero n -> div2 n `LT` n
div2_lt (S 0) SIsNonZero = LTESucc LTEZero
div2_lt (S (S k)) SIsNonZero = div2_lte k |>
  |~~ (div2 k `LTE` k)
  ~~> (S (S (div2 k)) `LTE` S (S k)) ... (LTESucc . LTESucc)

descent : (m, p : Nat) ->
  (nz_m : NonZero m) ->
  (h : sq m = dbl (sq p)) ->
  Accessible LT m -> Void
descent 0 _ _ SIsNonZero _ (Access _) impossible
descent (S 0) 0 SIsNonZero s__z (Access rec) =
  uninhabited s__z
descent (S 0) (S k) SIsNonZero h (Access rec) =
  let
    sz__ss : (S Z = S (S (dbl (k + k * S k))))
    sz__ss := Calc $
      |~ S Z
      ~~ sq (S Z) ... Refl
      ~~ dbl (sq (S k)) ... ?j1
      ~~ dbl (S (k + k * S k)) ... Refl
      ~~ S (S (dbl (k + k * S k))) ... (dbl_S (k + k * S k))
  in uninhabited sz__ss
descent (S (S k)) p nz_m h (Access rec) =
  descent (S (div2 k)) (div2 p)
    SIsNonZero (descent_step (S (S k)) p h)
    (rec (S (div2 k)) (div2_lt (S (S k)) nz_m))


-- ==========
--  There is no m and n such that
--    NotZero n and sq m = dbl (sq n)
--  Hence, sqrt 2 is irrational.
-- ==========

%hint
nz_n_imp_nz_m : (m, n : Nat) -> NonZero n -> sq m = dbl (sq n) -> NonZero m
nz_n_imp_nz_m 0 (S n') SIsNonZero z__s = absurd z__s
nz_n_imp_nz_m (S k) (S n') SIsNonZero sq_m__d_sq_n = SIsNonZero

irrational_sqrt2 : (m, n : Nat) -> NonZero n -> Not (sq m = dbl (sq n))
irrational_sqrt2 m (S n') SIsNonZero sq_m__d_sq_n =
  descent m (S n')
      (nz_n_imp_nz_m m (S n') SIsNonZero sq_m__d_sq_n)
      sq_m__d_sq_n (sizeAccessible m)
