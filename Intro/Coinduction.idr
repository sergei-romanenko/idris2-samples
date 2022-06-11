module Intro.Coinduction

import Data.Stream

%default total

--
-- Streams
--

{-
data Stream : Type -> Type where
  (::) : a -> Inf (Stream a) -> Stream a
-}


Zeros : Stream Nat
Zeros =  Z :: Zeros

natsFrom : Nat -> Stream Nat
natsFrom n = n :: natsFrom (S n)

Ones : Stream Nat
Ones = S Z :: Ones

mapS : Stream Nat -> Stream Nat
mapS (x :: xs) = S x :: mapS xs

Ones' : Stream Nat
Ones' = mapS Zeros


--
-- Functions on infinite data.
--
-- See map, zipWith, take, repeat, iterate.

t5_zeros : take 5 Zeros = [0, 0, 0, 0, 0]
t5_zeros = Refl

t3_natsFrom2 : take 3 (natsFrom 2) = [2, 3, 4]
t3_natsFrom2 = Refl

i1_natsFrom2 : index 2 (natsFrom 2) = 4
i1_natsFrom2 = Refl

--
-- Bisimilarity
--

infix 5 ~~

data (~~) : Stream a -> Stream a -> Type where
  (::) : x = y -> Inf (Force xs ~~ Force ys) ->
    x :: xs ~~ y :: ys

b2cw : xs ~~ ys -> (k : Nat) -> Stream.index k xs = Stream.index k ys
b2cw (h :: hs) Z = h
b2cw (h :: hs) (S k) = b2cw hs k

-- A proof by coinduction (bisimilarity).

th1 : (k : Nat) -> (natsFrom k) ~~ (k :: natsFrom (S k))
th1 k = Refl :: Delay (th1 (S k))

Th2 : Zeros ~~ repeat Z
Th2 = Refl :: Delay Th2

T5_ones : take 5 Ones = [1, 1, 1, 1, 1]
T5_ones = Refl

T5_ones' : take 5 Ones' = [1, 1, 1, 1, 1]
T5_ones' = Refl

Ones_Ones' : Ones ~~ map S Zeros
Ones_Ones' = Refl :: Ones_Ones'

eq_Zeros : Zeros = Z :: Zeros
eq_Zeros = Refl

map_repeat : (f : a -> b) -> (x : a) ->
  map f (repeat x) ~~ repeat (f x)
map_repeat f x = Refl :: map_repeat f x
