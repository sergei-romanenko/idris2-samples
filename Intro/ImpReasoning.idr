module Intro.ImpReasoning

prefix 1  |~~
infixl 0  ~~>
infix  1  ...
infixr 0 |>

%default total

-- Implication is a preorder relation...

public export
(|~~) : (0 a : Type) -> (a -> a)
(|~~) a = id

public export
(~~>) : (p : a -> b) -> (q : b -> c) -> (a -> c)
(~~>) p q = q . p

public export
(...) : (0 b : Type) -> (a -> b) -> (a -> b)
(...) b xy = xy

public export
(|>) : forall a, b. (x : a) -> (f : a -> b) -> b
(|>) x f = f x


namespace Examples

  tr1 : (p : a -> b) -> (q : b -> c) -> (a -> c)
  tr1 p q =
    |~~ a
    ~~> b ... (p)
    ~~> c ... (q)

  tr2 : (p : a -> b) -> (q : b -> c) -> (a -> c)
  tr2 p q =
    p ~~> q

  tr3 : (x : a) -> (p : a -> b) -> b
  tr3 x p = x |>
    |~~ a
    ~~> b ... (p)
