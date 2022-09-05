module ElabEven

import Decidable.Decidable
import Data.Maybe
import Language.Reflection
-- import Language.Reflection.Syntax
-- import Language.Reflection.Pretty

%language ElabReflection

%default total

-- Even

data Even : Nat -> Type where
  Even0 : Even 0
  Even2 : Even n -> Even (2 + n)

Ev2 : Even 2
Ev2 = Even2 Even0

Ev4 : Even 4
Ev4 = Even2 (Even2 Even0)

notEven1 : Even 1 -> Void
notEven1 Even0 impossible
notEven1 (Even2 _) impossible

invEven2 : Even (2 + n) -> Even n
invEven2 (Even2 even_n) = even_n

-- decEven

decEven : (n : Nat) -> Dec (Even n)
decEven Z = Yes Even0
decEven (S Z) = No notEven1
decEven (S (S n)) with (decEven n)
  _ | Yes even_n = Yes (Even2 even_n)
  _ | No not_even_n =
    No (\even_ssn => not_even_n (invEven2 even_ssn))

fromYes : {0 p : Type} -> (dp : Dec p) -> {auto isY : IsYes dp} -> p
fromYes (Yes prf) {isY = ItIsYes} = prf

Ev8dec : Even 8
Ev8dec = fromYes (decEven 8)

-- maybeEven

maybeEven : (n : Nat) -> Maybe (Even n)
maybeEven Z = Just Even0
maybeEven (S Z) = Nothing
maybeEven (S (S n)) with (maybeEven n)
  _ | Nothing = Nothing
  _ | (Just even_n) = Just (Even2 even_n)

Ev8mb : Even 8
Ev8mb = fromJust $ maybeEven 8

-- elabEven

elabEven : (k : Nat) -> Elab (Even k)
elabEven Z = pure Even0
elabEven (S Z) = fail "Odd arg"
elabEven (S (S k)) = do
  even_k <- elabEven k
  pure (Even2 even_k)

elabEv2 : Even 2
elabEv2 = %runElab (elabEven 2)

-- elabEv3 : Even 3
-- elabEv3 = %runElab (elabEven 3)

%macro
proveEven : {n : Nat} -> Elab (Even n)
proveEven = elabEven n

proveEv4 : Even 4
proveEv4 = proveEven
