module ElabEven

import Language.Reflection
-- import Language.Reflection.Syntax
-- import Language.Reflection.Pretty

%language ElabReflection

%default total

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

decEven : (n : Nat) -> Dec (Even n)
decEven Z = Yes Even0
decEven (S Z) = No notEven1
decEven (S (S n)) with (decEven n)
  decEven (S (S n)) | Yes even_n = Yes (Even2 even_n)
  decEven (S (S n)) | No not_even_n =
    No (\even_ssn => not_even_n (invEven2 even_ssn))

FromYes : {p : Type} -> (dp : Dec p) -> Type
FromYes {p} (Yes prf) = p
FromYes (No contra) = ()

fromYes : {0 p : Type} -> (dp : Dec p) -> FromYes dp
fromYes (Yes prf) = prf
fromYes (No contra) = ()

Ev8 : Even 8
Ev8 = fromYes (decEven 8)

maybeEven : (n : Nat) -> Maybe (Even n)
maybeEven Z = Just Even0
maybeEven (S Z) = Nothing
maybeEven (S (S n)) with (maybeEven n)
  maybeEven (S (S n)) | Nothing = Nothing
  maybeEven (S (S n)) | (Just even_n) = Just (Even2 even_n)

mbEv8 : maybeEven 8 = Just (Even2 (Even2 (Even2 (Even2 Even0))))
mbEv8 = Refl

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
