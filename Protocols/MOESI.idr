module Protocols.MOESI

State : Type
State = (Nat, Nat, Nat, Nat, Nat)

data Reachable : State -> Type where
  Start : Reachable (i, 0, 0, 0, 0)
  T1 : Reachable (S i, m, s, e, o') -> Reachable (i, 0, S (s + e), 0, m + o')
  T2 : Reachable (i, m, s, S e, o') -> Reachable (i, S m, s, e, o')
  T3 : Reachable (i, m, S s, e, o') -> Reachable (i + m + s + e + o', 0, 0, S 0, 0)
  T4 : Reachable (S i, m, s, e, o') -> Reachable (i + m + s + e + o', 0, 0, S 0, 0)

data Unsafe : State -> Type where
  U1 : Unsafe (i, S m, S s, e, o')
  U2 : Unsafe (i, S m, s, S e, o')
  U3 : Unsafe (i, S m, s, e, S o')
  U4 : Unsafe (i, S (S m), s, e, o')
  U5 : Unsafe (i, m, s, S (S e), o')

data Config : State -> Type where
  C1 : Config(_, 0, 0, S 0, 0)
  C2 : Config(_, S 0, 0, 0, 0)
  C3 : Config(_, 0, _, 0, _)


--
-- A proof of `valid` that mimics a proof by supercompilation.
--

-- Any reachable state is covered by a configuration

inclusion: (r : Reachable s) -> Config s
inclusion Start = C3
inclusion (T1 r) = C3
inclusion (T2 r) with (inclusion r)
  inclusion (T2 r) | C1 = C2
inclusion (T3 r) = C1
inclusion (T4 r) = C1

-- Any state, that is covered by a configuration, is not unsafe.

safety: (c : Config s) -> (u : Unsafe s) -> Void
safety C1 U1 impossible
safety C1 U2 impossible
safety C1 U3 impossible
safety C1 U4 impossible
safety C1 U5 impossible
safety C2 U1 impossible
safety C2 U2 impossible
safety C2 U3 impossible
safety C2 U4 impossible
safety C2 U5 impossible
safety C3 U1 impossible
safety C3 U2 impossible
safety C3 U3 impossible
safety C3 U4 impossible
safety C3 U5 impossible

-- Any reachable state is not unsafe.

valid: (r : Reachable s) -> (u : Unsafe s) -> Void
valid = safety . inclusion

--
-- A direct proof, which is mysterious...
--

valid': (r : Reachable s) -> (u : Unsafe s) -> Void
valid' (T2 (T2 r)) U1 = valid' r U5
valid' (T2 r) U2 = valid' r U5
valid' (T2 (T2 r)) U3 = valid' r U5
valid' (T2 r) U4 = valid' r U2
valid' (T2 r) U5 = valid' r U5
