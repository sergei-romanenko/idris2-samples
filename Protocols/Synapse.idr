module Protocols.Synapse

%default total

State : Type
State = (Nat, Nat, Nat)

data Reachable : State -> Type where
  Start : Reachable(i, 0, 0)
  T1 : Reachable(S i, d, v) -> Reachable(i + d, 0, S v)
  T2 : Reachable(i, d, S v) -> Reachable(i + d + v, S 0, 0)
  T3 : Reachable(S i, d, v) -> Reachable(i + d + v, S 0, 0)

data Unsafe : State -> Type where
  U1 : Unsafe(i, S d, S v)
  U2 : Unsafe(i, S (S d), v)

data Config : State -> Type where
  C1 : Config(i, S 0, 0)
  C2 : Config(i, 0, v)

--
-- A proof of `valid` that mimics a proof by supercompilation.
--

-- Any reachable state is covered by a configuration

inclusion: (r : Reachable s) -> Config s
inclusion Start = C2
inclusion (T1 _) = C2
inclusion (T2 _) = C1
inclusion (T3 _) = C1

-- Any state, that is covered by a configuration, is not unsafe.

safety: (c : Config s) -> (u : Unsafe s) -> Void
safety C1 U1 impossible
safety C1 U2 impossible
safety C2 U1 impossible
safety C2 U2 impossible

-- Any reachable state is not unsafe.

valid: (r : Reachable s) -> (u : Unsafe s) -> Void
valid = safety . inclusion

--
-- A direct proof, which is mysterious...
--

valid': (r : Reachable s) -> (u : Unsafe s) -> Void
valid' Start U1 impossible
valid' Start U2 impossible
valid' (T1 _) U1 impossible
valid' (T1 _) U2 impossible
valid' (T2 _) U1 impossible
valid' (T2 _) U2 impossible
valid' (T3 _) U1 impossible
valid' (T3 _) U2 impossible
