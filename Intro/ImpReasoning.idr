module Intro.ImpReasoning

infixl 0  ~>
prefix 1  |~
infix  1  ...

%default total

-- Implication is a preorder relation...

public export
(...) : (0 b : Type) -> (a -> b) -> (a -> b)
(...) b xy = xy

public export
(|~) : (0 a : Type) -> (a -> a)
(|~) a = id

public export
(~>) : (p : a -> b) -> (q : b -> c) -> (a -> c)
(~>) p q = q . p

tr : (p : a -> b) -> (q : b -> c) -> (a -> c)
tr p q =
  |~ a
  ~> b ... (p)
  ~> c ... (q)
