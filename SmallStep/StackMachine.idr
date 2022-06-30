--
-- Small-step operational semantics
-- making use of dependent types
--

{-
This (slightly modified) code is from

  Proof by Smugness
  by Conor on August 7, 2007.
  http://fplab.bitbucket.org/posts/2007-08-07-proof-by-smugness.html
-}

module SmallStep.StackMachine

import Syntax.PreorderReasoning
import Syntax.WithProof
import Data.Vect
import Data.Singleton
import Data.DPair

%default total

--
-- A Toy Language
--

infixl 8 +

data Tm : Type where
  Cst : (n : Nat) -> Tm
  (+) : (t1, t2 : Tm) -> Tm

-- Big-step evaluator

eval : Tm -> Nat
eval (Cst n) = n
eval (t1 + t2) = eval t1 + eval t2


-- Natural semantics

data Eval : (t : Tm) -> (n : Nat) -> Type where
  EvCst  : Eval (Cst n) n
  EvPlus : Eval t1 n1 -> Eval t2 n2 -> Eval (t1 + t2) (n1 + n2)

corr_eval : (t : Tm) -> Eval t (eval t)
corr_eval (Cst n) = EvCst
corr_eval (t1 + t2) = EvPlus (corr_eval t1) (corr_eval t2)

-- data Singleton : a -> Type where
--      Val : (x : a) -> Singleton x

eval_sg : (t : Tm) -> (0 e : Eval t n) -> Singleton n
eval_sg (Cst n) EvCst = Val n
eval_sg (t1 + t2) (EvPlus e1 e2) with (eval_sg t1 e1, eval_sg t2 e2)
  _ | (Val n1, Val n2) = Val (n1 + n2)

eval_ss : (t : Tm) -> Subset Nat (Eval t)
eval_ss (Cst n) = Element n EvCst
eval_ss (t1 + t2) with (eval_ss t1, eval_ss t2)
  _ | (Element n1 e1, Element n2 e2) =
    Element (n1 + n2) (EvPlus e1 e2)

--
-- Virtual machine
--

-- Program

-- The idea is to index code by initial and final stack depth
-- in order to ensure stack safety.

data Code : (i, j : Nat) -> Type where
  Seq  : (c1 : Code i j) -> (c2 : Code j k) -> Code i k
  Push : (n : Nat) -> Code i (1 + i)
  Add  : Code (2 + i) (1 + i)

-- State

Stack : Nat -> Type
Stack i = Vect i Nat

-- Interpreter

exec : (c : Code i j) -> (s : Stack i) -> Stack j
exec (Seq c1 c2) s = exec c2 (exec c1 s)
exec (Push n) s = n :: s
exec Add (n2 :: (n1 :: s)) = (n1 + n2) :: s

-- Compiler

compile : (t : Tm) -> Code i (1 + i)
compile (Cst n) = Push n
compile (t1 + t2) = Seq (Seq (compile t1) (compile t2)) Add

-- `Seq` is associative with respect to `exec`.

seq_assoc : exec (Seq (Seq c1 c2) c3) s = exec (Seq c1 (Seq c2 c3)) s
seq_assoc = Calc $
  |~ exec (Seq (Seq c1 c2) c3) s
  ~~ exec c3 (exec (Seq c1 c2) s) ...( Refl )
  ~~ exec c3 (exec c2 (exec c1 s)) ...( Refl )
  ~~ exec (Seq c2 c3) (exec c1 s) ...( Refl )
  ~~ exec (Seq c1 (Seq c2 c3)) s ...( Refl )

-- Here is another proof, which is shorter, but is more mysterious.

seq_assoc' : exec (Seq (Seq c1 c2) c3) s = exec (Seq c1 (Seq c2 c3)) s
seq_assoc' = Refl

-- `compile` is correct with respect to `exec`.

correct_compile : (t : Tm) -> (s : Stack i) ->
  exec (compile t) s = eval t :: s
correct_compile (Cst n) s = Calc $ -- Refl
  |~ exec (compile (Cst n)) s
  ~~ exec (Push n) s ... (Refl)
  ~~ n :: s ...( Refl )
  ~~ eval (Cst n) :: s ... (Refl)
correct_compile (t1 + t2) s = Calc $
  |~ exec (compile (t1 + t2)) s
  ~~ exec (Seq (Seq (compile t1) (compile t2)) Add) s
        ...( Refl )
  ~~ exec Add (exec (compile t2) (exec (compile t1) s))
        ...( Refl )
  ~~ exec Add (exec (compile t2) (eval t1 :: s))
        ...( cong (exec Add . exec (compile t2)) (correct_compile t1 s) )
  ~~ exec Add (eval t2 :: (eval t1 :: s)) 
        ...( cong (exec Add) (correct_compile t2 (eval t1 :: s)) )
  ~~ (eval t1 + eval t2) :: s
        ...( Refl )
  ~~ eval (t1 + t2) :: s
        ...( Refl )


-- Here is another proof, which is shorter, but is more mysterious.

correct_compile' : (t : Tm) -> (s : Stack i) ->
  exec (compile t) s = eval t :: s
correct_compile' (Cst n) s = Refl
correct_compile' (t1 + t2) s =
  the (exec (compile (t1 + t2)) s = eval (t1 + t2) :: s)
    $ id $
  the (exec Add (exec (compile t2) (exec (compile t1) s)) =
        (eval t1 + eval t2) :: s)
    $ rewrite correct_compile' t1 s in
  the (exec Add (exec (compile t2) (eval t1 :: s)) =
        (eval t1 + eval t2) :: s)
    $ rewrite correct_compile' t2 (eval t1 :: s) in
  the ((eval t1 + eval t2) :: s = (eval t1 + eval t2) :: s)
    $ Refl

--
-- A compiler that is correct "by construction".
--

ex_code : (t : Tm) ->
  Subset (Code i (1 + i)) (\c => (s : Stack i) -> exec c s = eval t :: s)
ex_code (Cst n) = Element (Push n) $ \s => Calc $
  |~ exec (Push n) s
  ~~ n :: s             ...( Refl )
  ~~ eval (Cst n) :: s  ...( Refl )
ex_code (t1 + t2) with (ex_code {i=i} t1, ex_code {i=1+i} t2)
  ex_code (t1 + t2) | (Element c1 p1, Element c2 p2) =
    Element (Seq (Seq c1 c2) Add) $ \s => Calc $
      |~ exec (Seq (Seq c1 c2) Add) s
      ~~ exec Add (exec c2 (exec c1 s))
          ...( Refl )
      ~~ exec Add (exec c2 (eval t1 :: s))
          ...( cong (exec Add . exec c2) (p1 s) )
      ~~ exec Add (eval t2 :: (eval t1 :: s))
          ...( cong (exec Add) (p2 (eval t1 :: s)) )
      ~~ eval t1 + eval t2 :: s
          ...( Refl )
      ~~ eval (t1 + t2) :: s
          ...( Refl )

--
-- `ex_code` produces the same code as `compile`.
-- But Idris is not capable of automatically extracting
-- `compile` from `ex_code` (unlike Coq).
--

corr_ex_code : (t : Tm) ->
  compile {i} t = (ex_code {i} t).fst
corr_ex_code {i} (Cst n) = Refl
corr_ex_code {i} (t1 + t2) =
  let
    (Element c1 p1 ** eq1) = @@ ex_code {i=i} t1
    (Element c2 p2 ** eq2) = @@ ex_code {i=1+i} t2
    corr1 = corr_ex_code {i=i} t1
    corr2 = corr_ex_code {i=1+i} t2
  in
  rewrite the (compile t1 = fst (ex_code t1)) corr1 in
  rewrite the (compile t2 = fst (ex_code t2)) corr2 in
  rewrite the (ex_code t1 = Element c1 p1) eq1 in
  rewrite the (ex_code t2 = Element c2 p2) eq2 in
  the (Seq (Seq c1 c2) Add = Seq (Seq c1 c2) Add) Refl

--
-- Compiling to a list of instructions
--

-- Instructions

data Inst : (i, j : Nat) -> Type where
  IPush : (n : Nat) -> Inst i (1 + i)
  IAdd  : Inst (2 + i) (1 + i)

-- Programs

infixr 5 #

data Prog : (i, j : Nat) -> Type where
  EOP : Prog i i
  (#) : (c : Inst i j) -> (p : Prog j k) -> Prog i k

-- Interpreter

p_exec : (p : Prog i j) -> (s : Stack i) -> Stack j
p_exec EOP s = s
p_exec (IPush n # p) s = p_exec p (n :: s)
p_exec (IAdd # p) (n2 :: n1 :: s) = p_exec p ((n1 + n2) :: s)

-- Compiler

p_compile : (t : Tm) -> (p : Prog (1 + i) j) -> Prog i j
p_compile (Cst n) p = IPush n # p
p_compile (t1 + t2) p =
  p_compile t1 (p_compile t2 (IAdd # p))

-- Code -> Prog

flatten : (c : Code i j) -> (p : Prog j k) -> Prog i k
flatten (Seq c1 c2) p = flatten c1 (flatten c2 p)
flatten (Push n) p = IPush n # p
flatten Add p = IAdd # p

-- `flatten` is correct.

flatten_correct' : (c : Code i j) -> (p : Prog j k) -> (s : Stack i) ->
  p_exec p (exec c s) = p_exec (flatten c p) s
flatten_correct' (Seq c1 c2) p s = Calc $
  |~ p_exec p (exec (Seq c1 c2) s)
  ~~ p_exec p (exec c2 (exec c1 s))
    ...( Refl )
  ~~ p_exec (flatten c2 p) (exec c1 s)
    ...( flatten_correct' c2 p (exec c1 s) )
  ~~ p_exec (flatten c1 (flatten c2 p)) s
    ...( flatten_correct' c1 (flatten c2 p) s )
  ~~ p_exec (flatten (Seq c1 c2) p) s
    ...( Refl )
flatten_correct' (Push n) p s =
  Refl {x = p_exec p (n :: s)}
flatten_correct' Add p (n2 :: n1 :: s) =
  Refl {x = p_exec p (n1 + n2 :: s)}

flatten_correct : (c : Code i j) -> (s : Stack i) ->
  exec c s = p_exec (flatten c EOP) s
flatten_correct c s = flatten_correct' c EOP s

-- compile ~ p_compile

compile_p_compile : (t : Tm) -> (p : Prog (1 + i) j) ->
  flatten (compile t) p = p_compile t p
compile_p_compile (Cst n) p =
  Refl{x = IPush n # p}
compile_p_compile (t1 + t2) p = Calc $
  |~ flatten (compile (t1 + t2)) p
  ~~ flatten (compile t1) (flatten (compile t2) (IAdd # p))
    ...( Refl )
  ~~ (p_compile t1 (flatten (compile t2) (IAdd # p)))
    ...( compile_p_compile t1 (flatten (compile t2) (IAdd # p)) )
  ~~ (p_compile t1 (p_compile t2 (IAdd # p)))
    ...( cong (p_compile t1) (compile_p_compile t2 (IAdd # p)) )
  ~~ (p_compile (t1 + t2) p)
    ...( Refl )
