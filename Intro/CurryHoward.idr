module CurryHoward

%default total

-- Implication = `->`.

namespace SKI

    I : p -> p
    I x = x

    K : p -> q -> p
    K x y = x

    S : (p -> q -> r) -> (p -> q) -> p -> r
    S x y z = (x z) (y z)

    I' : p -> p
    I' = S K (K {q = p})

mp : (p -> q) -> p -> q
mp f x = f x

comp : (p -> q) -> (q -> r) -> p -> r
comp f g x = g (f x)

comp' : (p -> q) -> (q -> r) -> p -> r
comp' f g = g . f

-- Conjunction = `Pair`.
-- A proof of (P , Q) is a proof of P and a proof of Q.

-- `Pair` is commutative.

pair_comm : (p , q) -> (q , p)
pair_comm (x, y) = (y, x)

infixr 3 &&&

(&&&) : (p -> q) -> (p -> r) -> p -> (q , r)
f &&& g = \x => (f x, g x)

pair_comm' : (p , q) -> (q , p)
pair_comm' = snd &&& fst

-- Disjunction = `Either`
-- A proof of `Either P Q` is either a proof of P labeled with `Left` or
-- a proof of Q labeled with `Right`.

-- `Either` is commutative.

either_comm : p `Either` q -> q `Either` p
either_comm (Left p) = Right p
either_comm (Right q) = Left q

either_comm' : p `Either` q -> q `Either` p
either_comm' = either Right Left

-- Distributivity of `Pair` over `Either`.

distrib_pe_1 :  (p , Either q r) -> Either (p , q) (p , r)
distrib_pe_1 (p, (Left q)) = Left (p, q)
distrib_pe_1 (p, (Right r)) = Right (p, r)

distrib_pe_2 :  (p , Either q r) -> Either (p , q) (p , r)
distrib_pe_2 (p, qr) =
  either (Left . MkPair p) (Right . MkPair p) qr

-- The other direction.

distrib_ep_1 : Either (p , q) (p , r) -> (p , (Either q r))
distrib_ep_1 (Left (p, q)) = (p , (Left q))
distrib_ep_1 (Right (p , r)) = (p , (Right r))

distrib_ep_2 : Either (p , q) (p , r) -> (p , (Either q r))
distrib_ep_2 = either (fst &&& (Left . snd))
                      (fst &&& (Right . snd))

-- True = `()` and has a trivial proof.

triviallyTrue : () -- Unit
triviallyTrue = () -- MkUnit

-- False = `Void` and has no proof.

triviallyFalse : Void
triviallyFalse = ?r

-- Negation = `Not`.

-- Not : Type -> Type
-- Not a = a -> Void

-- void : Void -> a
-- void _ impossible

-- Some basic facts about negation.

contradict : Not (p , Not p)
contradict (p, np) = void (np p)

contrapos : (p -> q) -> Not q -> Not p
contrapos pq nq p = nq (pq p)

-- We show that Peirce's law is equivalent to the Law of
-- Excluded Middle (EM).

em_i_peirce : ((r : Type) -> Either r (Not r)) ->
  (p, q : Type) -> ((p -> q) -> p) -> p
em_i_peirce e p q pq_p with (e p)
  _ | (Left p') = p'
  _ | (Right np') = pq_p (\p => void (np' p))

peirce_i_em : ((p, q : Type) -> ((p -> q) -> p) -> p) ->
  ((r : Type) -> Either r (Not r))
peirce_i_em h r =
  h (Either r (Not r)) Void
    (\r_nr => Right (\r => r_nr (Left r)))

-- Universal quantification. Given a type A, and a predicate P : A -> Type
--   (x : A) ->  P x means that (P a) is true (inhabited) for all (a : A).

all_pair_lem_1 : {A : Type} -> {P, Q : A -> Type} -> 
  ((a : A) -> (P a, Q a)) -> (((a : A) -> P a), ((a : A) -> Q a))
all_pair_lem_1 a_pq =
  ((\a => fst (a_pq a)), (\a => snd (a_pq a)))

all_pair_lem_2 : {A : Type} -> {P, Q : A -> Type} -> 
  (((a : A) -> P a) , ((a : A) -> Q a)) -> ((a : A) -> (P a, Q a)) 
all_pair_lem_2 (a_p, a_q) a =
  (a_p a, a_q a)

-- Existence. Given a type A, and a predicate P : A -> Type,
-- `DPair A P` is the type of dependent pairs MkDPair x f, such that
--  then (x : A) and (px : P x).
-- `(a : A ** P)` means `(a : DPair A (\a => P a)`
-- `a ** p` means `MkDPair a (\a => p)`

all_ex_lem_1 : forall p. ((x : a) -> p x -> q) -> (x ** p x) -> q
all_ex_lem_1 a_pa_q (a ** pa) = a_pa_q a pa

all_ex_lem_2 : forall p. ((x ** p x) -> q) -> (x : a) -> p x -> q
all_ex_lem_2 a'pa_q a pa = a'pa_q (a ** pa)

frobenius_to : {p : a -> Type} -> (x ** (q, p x)) -> (q, (x ** p x))
frobenius_to (x ** (q , px)) = (q, (x ** px))

frobenius_from : {p : a -> Type} -> (q, (x ** p x)) -> (x ** (q, p x))
frobenius_from (q, (x ** px)) = (x ** (q, px))
