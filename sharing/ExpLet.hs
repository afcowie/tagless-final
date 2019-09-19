{-# LANGUAGE NoMonomorphismRestriction #-}

-- * Adding explicit sharing to our DSL

module ExpLet where

import ExpF

-- * Why do we even need explicit sharing
-- * Help the human reader (cf. Principia Mathematica)

-- * Can't we just use Haskell's let?
-- Haskell's lets is certainly explicit and so clearly
-- helps the reader. Does it helps CSE eliminators?
-- Does it help tagless interpreters?

-- The multiplication-by-4 example written explicitly
-- * exp_mul4 = mul 4 (variable "i1")

exp_mul4 = 
 let x = variable "i1" in
 let y = add x x in
 add y y

-- * Question: Does Haskell guarantee sharing?
-- * Question: can we rely on memoization?

tree_mul4 = case exp_mul4 of ExpI t -> t
{-
  Add (Add (Variable "i1") (Variable "i1")) 
      (Add (Variable "i1") (Variable "i1"))
-}

dag_mul4 = run_expN exp_mul4
-- (2,DAG BiMap[(0,NVar "i1"),(1,NAdd 0 0),(2,NAdd 1 1)])

-- * //
-- * Haskell's let does work, sometimes!
-- The question about Haskell let is non-trivial because
-- it sometimes works.

-- To demonstrate how Haskell let helps some interpreters
-- but not the others, we define two tagless-final
-- interpreters.

-- One computes the size of an expression (the number of the
-- constructors)

-- * Haskell's let does help some DSL interpreters
-- * The size interpreter
newtype Size t = Size Int

instance Exp Size where
    constant _ = Size 1
    variable _ = Size 1
    add (Size x) (Size y) = Size (x+y+1)

Size size_mul4 = exp_mul4  -- 7

Size size_large = mul (2^30) (variable "i1")
-- 2147483647
-- Nearly instantaneous: only 0.01 secs

-- * The print interpreter
-- Another interpreter will print the expression
newtype Print t = Print (IO ())
instance Exp Print where
    constant = Print . putStr . show 
    variable = Print . putStr
    add (Print x) (Print y) = Print (x >> putStr " + " >> y)

-- This interpreter will take a long time to print
-- (mul (2^30) (variable "i1")), _even_ if we redirect
-- the output to /dev/null
Print print_mul4 = exp_mul4
-- i1 + i1 + i1 + i1
-- We see the duplication in the output, thus the duplication
-- of the effort to print. 
-- * Print pm30 = mul (2^30) (variable "i1")
-- Here, running will take a long time, even if we print to /dev/null
-- So, here Haskell's let did not help!

-- We thus need a sharing form in the DSL itself

-- * //
-- * Adding a new form let_ to our DSL
-- We extend the DSL language with a new expression form, let_,
-- to indicate the explicit sharing
-- Tagless-final interpreters are easily extensible
class ExpLet repr where
  let_ :: repr a -> (repr a -> repr b) -> repr b

-- Re-written exp_mul4 using the explicit sharing
exp_mul4' = 
 let_ (variable "i1") (\x ->
 let_ (add x x)       (\y->
 add y y))

-- * Extending the existing interpreters with let_
-- As one might expect, let_ is basically the reverse application
instance ExpLet R where
  let_ x f = f x

-- As expected, exp_mul4 with and without explicit sharing evaluate
-- to the same results. After all, sharing is an optimization,
-- it should not affect the results of DSL programs
val_mul4  = unR exp_mul4 [("i1",5)] -- 20
val_mul4' = unR exp_mul4' [("i1",5)] -- 20

-- * How to see sharing
-- We would like to `see' the sharing.
-- We have to define a show-like function then, an interpreter
-- of tagless-final expressions as strings.
-- Actually, we need a bit more than strings: to show sharing
-- (as let-expressions) we need a way to generate `pointers',
-- or local variable names.

type LetVarCount = Int                        -- counter for generating let-var-names
newtype S t = S{unS :: LetVarCount -> String}

instance Exp S where
    constant  = S . const . show
    variable  = S . const
    add e1 e2 = S(\c -> unS e1 c ++ " + " ++ unS e2 c)

instance ExpLet S where
    let_ e f  = S(\c -> let vname = "v" ++ show c
                        in unwords ["let",vname,"=",unS e c,
                                    "in",unS (f (S (const vname))) (succ c)])

run_expS :: S t -> String
run_expS (S m) = m 0

sh_mul4  = run_expS exp_mul4
-- "i1 + i1 + i1 + i1"

sh_mul4' = run_expS exp_mul4'
-- "let v0 = i1 in let v1 = v0 + v0 in v1 + v1"

-- * //
-- * Payoff: extending the N interpreter to handle explicit sharing
-- Sharing a computation means performing a computation and sharing 
-- result. The code below says exactly that.
instance ExpLet N where
    let_ e f = N(do
                 x <- unN e
                 unN $ f (N (return x)))

-- Now, we can evaluate exp_mul4' as a DAG
-- The result is the same as dag_mul4.
dag_mul4' = run_expN exp_mul4'
-- (2,DAG BiMap[(0,NVar "i1"),(1,NAdd 0 0),(2,NAdd 1 1)])

-- * Benchmarking
-- To really see the difference, we need bigger multiplications

-- We don't want to write the expressions like |exp_mul4'| by hand,
-- we want to generate them.
-- We rewrite the |mul| generator to use the explicit sharing.
-- The difference from |mul| is on the last-but-one line.
mul' :: (ExpLet repr, Exp repr) => Int -> repr Int -> repr Int
mul' 0 _ = constant 0
mul' 1 x = x
mul' n x | n `mod` 2 == 0 = let_ x (\x' -> mul' (n `div` 2) (add x' x'))
mul' n x = add x (mul' (n-1) x)

-- Is there another way to write mul'?
-- mul' n x | n `mod` 2 == 0 = let_ (add x x) (\y -> mul' (n `div` 2) y)
-- "let v0 = i1 + i1 in let v1 = v0 + v0 in v1"

sh_mul4'' = run_expS (mul' 4 (variable "i1"))
-- "let v0 = i1 in let v1 = v0 + v0 in v1 + v1"

-- * //
-- * Benchmarking. Compare with bench12 and bench13 from ExpF.hs
bench_mul' n = do_bench $
               run_expN (mul' n (variable "i"))

bench12 = bench_mul' (2^12)
bench13 = bench_mul' (2^13)

-- The exponential speed-up is apparent
{-
*ExpLet> bench12
13
(0.02 secs, 3171764 bytes)
*ExpLet> bench13
14
(0.01 secs, 534548 bytes)
-}

-- The mul (2^30) is the expression tree with 2^30 leaves!
{-
*ExpLet> bench_mul' (2^20)
21
(0.01 secs, 1585752 bytes)
*ExpLet> bench_mul' (2^30)
31
(0.01 secs, 1055932 bytes)
-}

-- * Some sharing is left to discover:
{-
*ExpLet> run_expS (mul' 15 (variable "i"))
 "i + let v0 = i in v0 + v0 + 
      let v1 = v0 + v0 in v1 + v1 + let v2 = v1 + v1 in v2 + v2"
-}

-- It is found and eliminated
{-
*ExpLet> run_expN (mul' 15 (variable "i"))
(6,DAG BiMap[
   (0,NVar "i"),
   (1,NAdd 0 0),
   (2,NAdd 1 1),
   (3,NAdd 2 2),
   (4,NAdd 2 3),
   (5,NAdd 1 4),
   (6,NAdd 0 5)])
-}

-- rather quickly:
{-
*ExpLet> bench_mul' (2^30-1)
59
(0.01 secs, 1078232 bytes)
-}


main = do
       print tree_mul4
       print dag_mul4
       print val_mul4
       print val_mul4'
       print sh_mul4'
       print sh_mul4''

       print bench13

