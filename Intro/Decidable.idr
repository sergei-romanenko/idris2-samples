module Intro.Decidable

import Data.Nat
import Data.Vect
import Decidable.Equality

--
-- Evenness
--

data Even : Nat -> Type where
  Ev0 : Even Z
  Ev2 : (e : Even n) -> Even (S (S n))

even10 : Even 10
even10 = Ev2 (Ev2 (Ev2 (Ev2 (Ev2 Ev0))))

%hint
ev2Inv : Even (S (S n)) -> Even n
ev2Inv (Ev2 e) = e

-- data Dec : Type -> Type where
--   Yes : (prf : prop) -> Dec prop
--   No  : (contra : Not prop) -> Dec prop

%hint
notEven1 : Even (S Z) -> Void
notEven1 Ev0 impossible
notEven1 (Ev2 _) impossible

Uninhabited (Even (S Z)) where
  uninhabited Ev0 impossible
  uninhabited (Ev2 _) impossible

decEven : (n : Nat) -> Dec (Even n)
decEven Z = Yes Ev0
decEven (S Z) = No absurd -- No notEven1
decEven (S (S n')) with (decEven n')
  decEven (S (S n')) | (Yes even_n') =
    Yes $ Ev2 even_n'
  decEven (S (S n')) | (No not_even_n') =
    No $ \even_n => not_even_n' (ev2Inv even_n)

soundnessEvenY : (p : _) -> decEven n = Yes p -> Even n
soundnessEvenY p _ = p

soundnessEvenN : (np : _) -> decEven n = No np -> Not (Even n)
soundnessEvenN np _ p = np p

decEven4 : decEven 4 = Yes (Ev2 (Ev2 Ev0))
decEven4 = Refl

decEven1 : decEven 1 = No (\even1 => absurd even1)
decEven1 = Refl

decEven3 : decEven 3 = No (\even3 => absurd (ev2Inv even3))
decEven3 = Refl

decEven5 : decEven 5 = No (\even5 => absurd (ev2Inv (ev2Inv even5)))
decEven5 = Refl

decPair : Dec p -> Dec q -> Dec ((p, q))
decPair (Yes p) (Yes q) = Yes (p, q)
decPair _       (No nq) = No (\pq => nq (snd pq))
decPair (No np) _       = No (\pq => np (fst pq))

decEitherNN : (p -> Void) -> (q -> Void) -> Either p q -> Void
decEitherNN np nq (Left p) = np p
decEitherNN np nq (Right q) = nq q

decEither : Dec p -> Dec q -> Dec (Either p q)
decEither (Yes p) _       = Yes (Left p)
decEither _       (Yes q) = Yes (Right q)
decEither (No np) (No nq) = No (decEitherNN np nq)

decNot : Dec p -> Dec (Not p)
decNot (Yes p) = No (\np => np p)
decNot (No np) = Yes np

-- data LTE  : (n, m : Nat) -> Type where
--   LTEZero : LTE Z    right
--   LTESucc : LTE left right -> LTE (S left) (S right)

lte_pred : LTE (S m) (S n) -> LTE m n
lte_pred (LTESucc lte_mn) = lte_mn

decNatLTE : (m, n : _) -> Dec (m `LTE` n)
decNatLTE Z n = Yes LTEZero
decNatLTE (S m') Z = No (\lte_sz => absurd lte_sz)
decNatLTE (S m') (S n') with (decNatLTE m' n')
  _ | (Yes lte) = Yes (LTESucc lte)
  _ | (No nlte) = No (nlte . lte_pred)

eitherLTE : (m, n : Nat) ->  Either (m `LTE` n) (n `LT` m)
eitherLTE Z n = Left LTEZero
eitherLTE (S m') Z = Right (LTESucc LTEZero)
eitherLTE (S m') (S n') with (eitherLTE m' n')
  _ | (Left lte_m'n') = Left (LTESucc lte_m'n')
  _ | (Right lt_n'm') = Right (LTESucc lt_n'm')

--
-- Views
--

-- Parity

data Parity : Nat -> Type where
  PEven : (k : Nat) -> Parity (k + k)
  POdd  : (k : Nat) -> Parity (S (k + k))

parity : (n : Nat) -> Parity n
parity Z = PEven Z
parity (S n') with (parity n')
  parity (S (k + k)) | (PEven k) =
    POdd k
  parity (S (S (k + k))) | (POdd k) =
    rewrite plusSuccRightSucc k k in
    PEven (S k)

half : (n : Nat) -> Nat
half n with (parity n)
  half (k + k) | (PEven k) = k
  half (S (k + k)) | (POdd k) = k

--
-- Information propagation
--

namespace AddVect1

  addVec : (xs : Vect n Nat) -> (ys : Vect n Nat) -> Vect n Nat
  addVec = zipWith (+)

namespace AddVect2

  addVec :
    {m : _} -> (xs : Vect m Nat) ->
    {n : _} -> (ys : Vect n Nat) -> Maybe (Vect m Nat)
  {-
  -- This doesn't work! No information propagation about m≡n . :-(
  addVec xs ys =
    if m /= n then Nothing
              else Just (zipWith (+) xs ys)
  -}
  addVec {m} xs {n} ys with (decEq m n)
    _ | (No ne) = Nothing
    _ | (Yes m_eq_n) =
      let ys' : Vect m Nat
          ys' = rewrite m_eq_n in ys
      in
      Just (zipWith (+) xs ys')

namespace AddVec3

  addVec :
    {m : _} -> (xs : Vect m Nat) ->
    {n : _} -> (ys : Vect n Nat) -> Maybe (Vect m Nat)
  addVec {m} xs {n} ys with (decEq m n)
    addVec xs ys | (No ne) = Nothing
    addVec xs ys | (Yes m_eq_n) =
      let ys' : Vect m Nat
          ys' = replace {p = \k => Vect k Nat} (sym m_eq_n) ys
      in
      Just (zipWith (+) xs ys')
