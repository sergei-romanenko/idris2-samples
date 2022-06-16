module Protocols.SynapseDetailed

%default total

data Synapse : Nat -> Nat -> Nat -> Type where
  Start : (i : Nat) -> Synapse i 0 0
  T1 : (i, d, v : Nat) -> Synapse (S i) d v -> Synapse (i + d) 0 (S v)
  T2 : (i, d, v : Nat) -> Synapse i d (S v) -> Synapse (i + d + v) (S 0) 0
  T3 : (i, d, v : Nat) -> Synapse (S i) d v -> Synapse (i + d + v) (S 0) 0

data Unsafe : Nat -> Nat -> Nat -> Type where
  U1 : (i, d, v : Nat) -> Unsafe i (S d)     (S v)
  U2 : (i, d, v : Nat) -> Unsafe i (S (S d)) v

data Config : Nat -> Nat -> Nat -> Type where
  C1 : (i : Nat)    -> Config i (S 0) 0
  C2 : (i, v : Nat) -> Config i  0    v

--
-- A proof of `valid` that mimics a proof by supercompilation.
--

-- Any reachable state is covered by a configuration

inclusion: Synapse i d v -> Config i d v
inclusion (Start i) = C2 i 0
inclusion (T1 i d v x) = C2 (i + d) (S v)
inclusion (T2 i d v x) = C1 ((i + d) + v)
inclusion (T3 i d v x) = C1 ((i + d) + v)

-- Any state, that is covered by a configuration, is not unsafe.

safety: Config i d v -> Unsafe i d v -> Void
safety (C1 _) (U1 _ _ _) impossible
safety (C2 _ _) (U1 _ _ _) impossible
safety (C1 _) (U2 _ _ _) impossible
safety (C2 _ _) (U2 _ _ _) impossible

-- Any reachable state is not unsafe.

valid: Synapse i d v -> Unsafe i d v -> Void
valid = safety . inclusion

--
-- A direct proof, which is mysterious...
--

valid': Synapse i d v -> Unsafe i d v -> Void
valid' (Start _) (U1 _ _ _) impossible
valid' (Start _) (U2 _ _ _) impossible
valid' (T1 _ _ _ _) (U1 _ _ _) impossible
valid' (T1 _ _ _ _) (U2 _ _ _) impossible
valid' (T2 _ _ _ _) (U1 _ _ _) impossible
valid' (T2 _ _ _ _) (U2 _ _ _) impossible
valid' (T3 _ _ _ _) (U1 _ _ _) impossible
valid' (T3 _ _ _ _) (U2 _ _ _) impossible
