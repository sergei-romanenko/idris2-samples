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
-- Suppose that m*m = 2 * (p*p).
--
-- 2 * (p*p) is even -> m*m is even -> m is even.
--
-- Let m = 2 * n. Then
--
-- (2*n)*(2*n) = 2 * (p*p) -> 4*(n*n) = 2*(p*p) -> 2*(n*n) = p*p ->
-- p*p = 2*(n*n).
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


-- module Corbineau.Sqrt2 where

-- open import Data.Nat
--   using (Nat; Z; suc; _+_; _*_; ⌊_/2⌋; _<′_; ≤′-refl; _≟_)
-- open import Data.Nat.Properties.Simple
--   using (+-suc; +-assoc; *-comm; distribʳ-*-+; +-right-identity)
-- open import Data.Nat.Properties
--   using (s≤′s; ⌊n/2⌋≤′n)
-- open import Data.Sum as Sum
--   using (_⊎_; inj₁; inj₂; [_,_]′)
-- open import Data.Empty
--   using (⊥; ⊥-elim)

-- open import Function
--   using (_∘_; _$_)
-- import Function.Related as Related

-- open import Relation.Nullary
--   using (Dec; yes; no; ¬_)
-- open import Relation.Binary.PropositionalEquality as P
--   using (_≡_; _≢_; refl; cong; cong₂; subst; sym; module =-Reasoning)

-- open import Induction.WellFounded
--   using (Acc; acc)
-- open import Induction.Nat
--   using (<′-well-founded)

import Data.Nat
import Control.WellFounded
import Syntax.PreorderReasoning
import Decidable.Equality

%default total

double : Nat -> Nat
double n = n + n

sq : Nat -> Nat
sq n = n * n

div2 : (n : Nat) -> Nat
div2 Z = Z
div2 (S Z) = Z
div2 (S (S n)) = S (div2 n)

%hint
double_S : (n : Nat) -> double (S n) = S (S (double n))
double_S n = Calc $
  |~ double (S n)
  ~~ S (n + S n)      ... Refl
  ~~ S (S (n + n))    ... (cong S $ sym $ plusSuccRightSucc n n)
  ~~ S (S (double n)) ... Refl

%hint
div2_double : (n : Nat) -> div2 (double n) = n
div2_double Z = Refl
div2_double (S n) = Calc $
  |~ div2(double (S n))
  ~~ div2 (S (S (double n))) ... (cong div2 (double_S n))
  ~~ S (div2 (double n))     ... Refl
  ~~ S n                     ... (cong S (div2_double n))

%hint
double_inj : double m = double n -> m = n
double_inj eq_2m_2n = Calc $
  |~ m
  ~~ div2 (double m) ... (sym $ div2_double m)
  ~~ div2 (double n) ... (cong div2 eq_2m_2n)
  ~~ n               ... (div2_double n)

%hint
double_mult_l : double (m * n) = m * (double n)
double_mult_l = Calc $
  |~ double (m * n)
  ~~ double (n * m)    ... (cong double $ multCommutative m n)
  ~~ n * m + n * m     ... Refl
  ~~ (n + n) * m       ... (sym $ multDistributesOverPlusLeft n n m)
  ~~ m * (n + n)       ... (multCommutative (n + n) m)
  ~~ m * (double n)    ... Refl

%hint
double_mult_r : double (m * n) = (double m) * n
double_mult_r = Calc $
  |~ double (m * n)
  ~~ double (n * m)    ... (cong double $ multCommutative m n)
  ~~ n * (double m)    ... (double_mult_l)
  ~~ (double m) * n    ... (multCommutative n (double m))

mutual

  data Even : Nat -> Type where
    Even0 : Even Z
    Even1 : Odd n -> Even (S n)

  data Odd : Nat -> Type where
    Odd1 : Even n -> Odd (S n)

Uninhabited (Odd Z) where
  uninhabited (Odd1 _) impossible

either_even_odd : (n : Nat) -> Either (Even n) (Odd n)
either_even_odd Z = Left Even0
either_even_odd (S n) with (either_even_odd n)
  _ | (Left even_n) = Right (Odd1 even_n)
  _ | (Right odd_n) = Left (Even1 odd_n)

even_double : (n : Nat) -> Even (double n)
even_double Z = Even0
even_double (S Z) = Even1 (Odd1 Even0)
even_double (S (S n)) =
  the (Even (double (S (S n)))) $
    rewrite double_S (S n) in
  the (Even (S (S (double (S n))))) $
    (Even1 . Odd1) $
  the (Even (double (S n))) $
    rewrite double_S n in
  the (Even (S (S (double n)))) $
    (Even1 . Odd1) $
  the (Even (double n)) $
    even_double n

%hint
even_double_div2 : Even n -> double (div2 n) = n
even_double_div2 Even0 = ?even_double_div2_rhs_0
even_double_div2 (Even1 (Odd1 {n = n} even_n)) = Calc $
  |~ double (div2 (S (S n)))
  ~~ double (S (div2 n))     ... Refl
  ~~ S (S (double (div2 n))) ... (double_S (div2 n))
  ~~ S (S n)                 ... (cong (S . S) (even_double_div2 even_n))


%hint
even_even_plus : (m : Nat) -> Even m -> Even (m + n) -> Even n
even_even_plus 0 Even0 even_n = even_n
even_even_plus (S 0) (Even1 odd_Z) (Even1 odd_n) = absurd odd_Z
even_even_plus (S (S m)) (Even1 (Odd1 even_m)) (Even1 (Odd1 even_mn)) =
  even_even_plus m even_m even_mn


%hint
odd_even_mult : {m, n : Nat} -> Odd m -> Even (m * n) -> Even n
odd_even_mult (Odd1 Even0) even_1n =
  the (Even n) $
    rewrite sym $ plusZeroRightNeutral n in
  the (Even (n + 0)) $
    id
  the (Even (1 * n)) $
    even_1n
odd_even_mult (Odd1 (Even1 {n=m} odd_m)) even_nn_mn =
  the (Even n) $
    odd_even_mult odd_m $
  the (Even (m * n)) $
    even_even_plus (double n) (even_double n) $
  the (Even ((n + n) + m * n)) $
    rewrite sym $ plusAssociative n n (m * n) in
  the (Even (n + (n + m * n))) $
    even_nn_mn


%hint
even_sq : {n : Nat} -> Even (sq n) -> Even n
even_sq even_nn with (either_even_odd n)
  _ | Left even_n = even_n
  _ | Right odd_n = odd_even_mult odd_n even_nn


%hint
odd_double_div2 : {n : Nat} -> Odd n -> S (double (div2 n)) = n
odd_double_div2 (Odd1 Even0) = Refl
odd_double_div2 {n = S (S n)} (Odd1 (Even1 odd_n)) = Calc $
  |~ S (double (div2 (S (S n))))
  ~~ S (double (S (div2 n)))     ... Refl
  ~~ S (S (S (double (div2 n)))) ... (cong S (double_S (div2 n)))
  ~~ S (S n)                     ... (cong (S . S) (odd_double_div2 odd_n))


%hint
even_dd_sq_div2 : {n : Nat} -> Even n ->
  double (double (sq (div2 n))) = sq n
even_dd_sq_div2 even_n = Calc $
  |~ double (double (sq (div2 n)))
  ~~ double (double (div2 n * div2 n)) ... Refl
  ~~ double (div2 n * double (div2 n)) ... (cong double double_mult_l)
  ~~ double (div2 n) * double (div2 n) ... (double_mult_r)
  ~~ sq n 
    ... (cong2 (*) (even_double_div2 even_n) (even_double_div2 even_n))


%hint
sq__0 :  {n : Nat} -> sq n = 0 -> n = 0
sq__0 {n = 0} Refl = Refl
sq__0 {n = (S n')} s__0 = absurd s__0


%hint
div2_lte : (n : Nat) -> div2 n `LTE`  n
div2_lte Z = LTEZero
div2_lte (S Z) = LTEZero
div2_lte (S (S n')) =
  LTESucc $ lteSuccRight $ div2_lte n'

%hint
div2_lt : (n : Nat) -> NonZero n -> div2 n `LT` n
div2_lt (S Z) SIsNonZero = LTESucc LTEZero
div2_lt (S (S n')) SIsNonZero =
   LTESucc $ LTESucc $ div2_lte n'

%hint
not_eq_0__nonzero : (k : Nat) -> Not (k = 0) -> NonZero k
not_eq_0__nonzero Z neq_0_0 = void (neq_0_0 Refl)
not_eq_0__nonzero (S k) neq_sk_0 = SIsNonZero

-- ==========
-- The most sophisticated part:
--   sq m = double (sq p) -> p = 0.
-- The proof is by reducing the problem to a "smaller" one:
--   sq (m/2) = sq (double(p/2)) -> p/2 = 0
-- ==========

covering
descent : (m, p : Nat) -> sq m = double (sq p) -> Accessible LT m -> p = 0
descent m p h (Access rec) with (decEq m Z)
  _ | Yes eq_m_0 =
    the (p = 0) $
      sq__0 $
    the (sq p = 0) $
      double_inj $
    the (double (sq p) = double 0) $
      id $
    the (double (sq p) = sq 0) $
      sym $
    the (sq 0 = double (sq p)) $
      replace {p = \t => sq t = double (sq p)} (eq_m_0) $
    the (sq m = double (sq p)) $
      h

  _ | No neq_m_0 =
    p__0
    where
      N : Nat
      N = div2 m
      Q : Nat
      Q = div2 p

      even_m : Even m
      even_m =
        the (Even m) $
          even_sq $
        the (Even (sq m)) $
          replace {p = Even} (sym h) $
        the (Even (double (sq p))) $
          even_double (sq p)

      dd_sq_n__sq_m : double (double (sq N)) = sq m
      dd_sq_n__sq_m = even_dd_sq_div2 even_m

      dd_sq_n__d_sq_p : double (double (sq N)) = double (sq p)
      dd_sq_n__d_sq_p = Calc $
        |~ double (double (sq N))
        ~~ sq m          ... ( dd_sq_n__sq_m )
        ~~ double (sq p) ... ( h )

      d_sq_n__sq_p : double (sq N) = sq p
      d_sq_n__sq_p = double_inj dd_sq_n__d_sq_p

      even_p : Even p
      even_p =
        the (Even p) $
          even_sq $
        the (Even (sq p)) $
          replace {p = Even} d_sq_n__sq_p $
        the (Even (double (sq N))) $
          even_double (sq N)

      dd_sq_n__ddd_sq_q :
        double (double (sq N)) = double (double (double (sq Q)))
      dd_sq_n__ddd_sq_q = Calc $
        |~ double (double (sq N))
        ~~ double (sq p)
          ... ( dd_sq_n__d_sq_p )
        ~~ double (double (double (sq Q)))
          ... ( cong double (sym $ even_dd_sq_div2 even_p) )

      sq_n__d_sq_q : sq N = double (sq Q)
      sq_n__d_sq_q = double_inj (double_inj dd_sq_n__ddd_sq_q)

      nonZero_m : NonZero m
      nonZero_m = not_eq_0__nonzero m neq_m_0

      q__0 : Q = 0
      q__0 = descent N Q sq_n__d_sq_q (rec (div2 m) (div2_lt m nonZero_m))

      p__0 : p = 0
      p__0 = Calc $
        |~ p
        ~~ double Q  ... (sym $ even_double_div2 even_p)
        ~~ double 0  ... (cong double q__0)
        ~~ 0         ... Refl

      q__0_imp_p_0 : q = 0 -> p = 0
      q__0_imp_p_0 q__0 = Calc $
        |~ p
        ~~ double Q  ... (sym $ even_double_div2 even_p)
        ~~ double 0  ... (cong double q__0)
        ~~ 0         ... Refl

-- ==========
--  There is no m and n such that
--    n ≢ 0 and msq = mult2nsq
--  Hence, sqrt 2 is irrational.
-- ==========

covering
irrational_sqrt2 : (m, n : Nat) -> NonZero n -> Not (sq m = double (sq n))
irrational_sqrt2 m (S n') SIsNonZero sq_m__d_sq_n = absurd sn__0
  where
    sn__0 : S n' = 0
    sn__0 = descent m (S n') sq_m__d_sq_n (sizeAccessible m)
