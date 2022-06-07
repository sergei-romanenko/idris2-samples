module Intro

import Syntax.PreorderReasoning

%hint
plus_z : (m : Nat) -> m = m + Z
plus_z Z =
  the (Z = Z + Z) Refl
plus_z (S m') =
  -- cong S (plus_z k)
  the (S m' = S m' + Z)
    $ id $
  the (S m' = S (m' + Z))
    $ cong S $
  the (m' = m' + Z)
    $ plus_z m'

%hint
plus_s : (m, n : Nat) -> S (m + n) = m + S n
plus_s Z n = Refl
plus_s (S m') n =
  -- cong S (plus_s m' n)
  the (S (S m' + n) = S m' + S n)
    $ id $
  the (S (S (m' + n)) = S (m' + S n))
    $ cong S $
  the (S (m' + n) = m' + S n)
    $ plus_s m' n

plus_comm : (m, n : Nat) -> m + n = n + m
plus_comm 0 n = plus_z n
plus_comm (S m') n =
  -- plus (S m') n = S (plus m' n) =  S (plus n m') = plus n (S m')
  the (S m' + n = n + S m')
    $ id
  the (S (m' + n) = n + S m')
    $ rewrite (plus_comm m' n) in
  the (S (n + m') = n + S m')
    $ rewrite plus_s n m' in
  the (n + S m' = n + S m')
    $ Refl

plus_comm' : (m, n : Nat) -> m + n = n + m
plus_comm' 0 n = plus_z n
plus_comm' (S m') n = Calc $
    |~ plus (S m') n
    ~~ S (plus m' n) ...( Refl )
    ~~ S (plus n m') ...( cong S (plus_comm' m' n) )
    ~~ plus n (S m') ...( plus_s n m' )
