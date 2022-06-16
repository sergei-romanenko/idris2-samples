module Protocols.DataRace

%default total

State : Type
State = (Nat, Nat, Nat)

data Reachable : State -> Type where
  Start : Reachable(out, 0, 0)
  T1 : Reachable(S out, 0, 0)    -> Reachable(out, S 0, 0)
  T2 : Reachable(S out, 0, scs)  -> Reachable(out, 0, S scs)
  T3 : Reachable(out, S cs, scs) -> Reachable(S out, cs, scs)
  T4 : Reachable(out, cs, S scs) -> Reachable(S out, cs, scs)

data Unsafe : State -> Type where
  U1 : Unsafe(out, S cs, S scs)

data Config : State -> Type where
  C1 : Config(out, 0, scs)
  C2 : Config(out, S 0, 0)

--
-- A proof of `valid` that mimics a proof by supercompilation.
--

-- Any reachable state is covered by a configuration

inclusion: {s : State} -> (r : Reachable s) -> Config s
inclusion Start = C1
inclusion (T1 r) = C2
inclusion (T2 r) = C1
inclusion (T3 r) with (inclusion r)
  _ | C2 = C1
inclusion (T4 r) with (inclusion r)
  _ | C1 = C1


-- Any state, that is covered by a configuration, is not unsafe.

safety: (c : Config s) -> (u : Unsafe s) -> Void
safety C1 U1 impossible
safety C2 U1 impossible

-- Any reachable state is not unsafe.

valid : {s : State} -> (r : Reachable s) -> (u : Unsafe s) -> Void
valid = safety . inclusion

--
-- A direct proof, which is mysterious...
--

valid': (r : Reachable c) -> (u : Unsafe c) -> Void
valid' (T3 r) U1 = valid' r U1
valid' (T4 r) U1 = valid' r U1
