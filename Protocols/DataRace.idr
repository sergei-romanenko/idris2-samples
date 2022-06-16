module Protocols.DataRace

%default total

data DataRace : Nat -> Nat -> Nat -> Type where
  Start : DataRace out 0 0
  T1 : DataRace (S out) 0 0    -> DataRace out (S 0) 0
  T2 : DataRace (S out) 0 scs  -> DataRace out 0 (S scs)
  T3 : DataRace out (S cs) scs -> DataRace (S out) cs scs
  T4 : DataRace out cs (S scs) -> DataRace (S out) cs scs

data Unsafe : Nat -> Nat -> Nat -> Type where
  U1 : Unsafe out (S cs) (S scs)

data Config : Nat -> Nat -> Nat -> Type where
  C1 : Config out 0 scs
  C2 : Config out (S 0) 0

--
-- A proof of `valid` that mimics a proof by supercompilation.
--

-- Any reachable state is covered by a configuration

inclusion: (out, cs, scs : Nat) -> DataRace out cs scs -> Config out cs scs
inclusion out 0 0 Start = C1
inclusion out 1 0 (T1 x) = C2
inclusion out 0 (S scs) (T2 x) = C1
inclusion (S out) cs scs (T3 x) with (inclusion out (S cs) scs x)
  inclusion (S out) 0 0 (T3 x) | C2 = C1
inclusion (S out) cs scs (T4 x) with (inclusion out cs (S scs) x)
  inclusion (S out) 0 scs (T4 x) | C1 = C1

-- The same, but with implicit parameters.

inclusion': {out, cs, scs : Nat} -> DataRace out cs scs -> Config out cs scs
inclusion' Start = C1
inclusion' (T1 x) = C2
inclusion' (T2 x) = C1
inclusion' (T3 {cs} {scs} x) with (inclusion' x)
  inclusion' (T3 {cs = 0} {scs = 0} x) | C2 = C1
inclusion' (T4 {cs} x) with (inclusion' x)
  inclusion' (T4 {cs = 0} x) | C1 = C1


-- Any state, that is covered by a configuration, is not unsafe.

safety: Config out cs scs -> Unsafe out cs scs -> Void
safety C1 U1 impossible
safety C2 U1 impossible

-- Any reachable state is not unsafe.

partial
valid: (out, cs, scs : Nat) -> DataRace out cs scs -> Unsafe out cs scs -> Void
valid out cs scs = safety . inclusion out cs scs

--
-- A direct proof, which is mysterious...
--

valid': DataRace i d v -> Unsafe i d v -> Void
valid' (T3 x) U1 = valid' x U1
valid' (T4 x) U1 = valid' x U1
