module Intro.ImpReasoning2

import Control.Relation
import Control.Order
import Syntax.PreorderReasoning.Generic

%default total

-- Implication is a preorder relation...

namespace Imp
  qed : (a : Type) -> (a -> a)
  qed a = id
  step : (a : Type) -> (p : a -> b) -> (q : b -> c) -> (a -> c)
  step a p q = q . p

  tr : {a, b, c : Type} -> (p : a -> b) -> (q : b -> c) -> (a -> c)
  tr {a} {b} {c} p q = step a p $ step b q $ qed c

infixl 0  ~>

public export
data (~>) : (a, b : Type) -> Type where
  MkImp : (f : a -> b) -> a ~> b

public export
Reflexive Type (~>) where
  reflexive = MkImp id

public export
Transitive Type (~>) where
  transitive (MkImp p) (MkImp q) = MkImp (q . p)

public export
Preorder Type (~>) where

tr : {a, b, c : Type} -> (p : a ~> b) -> (q : b ~> c) -> (a ~> c)
tr p q = CalcWith $
  |~ a
  <~ b ...(p)
  <~ c ...(q)
