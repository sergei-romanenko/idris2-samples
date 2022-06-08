module Intro

import Syntax.PreorderReasoning

%hint
plus_z : (m : Nat) -> m = m + Z
plus_z Z =
  the (Z = Z + Z)
    $ id $
  the (Z = Z)
    $ Refl
plus_z (S m') =
  the (S m' = S m' + Z)
    $ id $
  the (S m' = S (m' + Z))
    $ cong S $
  the (m' = m' + Z)
    $ plus_z m'


%hint
plus_s : (m, n : Nat) -> S (m + n) = m + S n
plus_s Z n =
  the (Z + S n = Z + S n)
    $ id $
  the (S n = S n)
    $ Refl
plus_s (S m') n =
  the (S (S m' + n) = S m' + S n)
    $ id $
  the (S (S (m' + n)) = S (m' + S n))
    $ cong S $
  the (S (m' + n) = m' + S n)
    $ plus_s m' n

plus_comm : (m, n : Nat) -> m + n = n + m
plus_comm Z n =
  the (Z + n = n + Z)
    $ id $
  the (n = n + Z)
    $ plus_z n
plus_comm (S m') n =
  the (S m' + n = n + S m')
    $ id $
  the (S (m' + n) = n + S m')
    $ rewrite (the (m' + n = n + m')
        $ plus_comm m' n) in
  the (S (n + m') = n + S m')
    $ rewrite the (S (n + m') = n + S m')
        $ plus_s n m' in
  the (n + S m' = n + S m')
    $ Refl

plus_comm' : (m, n : Nat) -> m + n = n + m
plus_comm' Z n = Calc $
  |~ Z + n
  ~~ n      ...( Refl )
  ~~ n + Z  ...( plus_z n )
plus_comm' (S m') n = Calc $
    |~ S m' + n
    ~~ S (m' + n)  ...( Refl )
    ~~ S (n + m')  ...( cong S (plus_comm' m' n) )
    ~~ n + S m'    ...( plus_s n m' )
