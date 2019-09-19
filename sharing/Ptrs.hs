-- Detecting sharing in embedded DSLs
-- Illustrating the three main approaches reviewed in
-- Alfonso Acosta's ForSyDe thesis

module Ptrs where

import Control.Monad.State

import Data.IORef                        -- for observable sharing
import System.IO.Unsafe

-- All three approaches are based on a sort of `pointer' comparison.
-- Or, on labeling expressions with unique pieces of data (e.g., integers)
-- that admit efficient comparison

-- Labeled expressions

type Lab = Int

data ExpL
   = AddL Lab ExpL ExpL
   | VariableL Lab String
   | ConstantL Lab Int
   deriving Show

-- ExpL expressions can be compared in constant time, by comparing the
-- labels, presumed unique. The full traversal is no longer needed
instance Eq ExpL where
    e1 == e2 = label e1 == label e2
     where
     label (AddL p _ _)    = p
     label (ConstantL p _) = p
     label (VariableL p _) = p

-- The first approach: manual labeling

-- Sample expressions
-- Manual labelling is clearly cumbersome and error-prone
-- (although Template Haskell greatly helps)
expL_a = AddL 3 (ConstantL 1 10) (VariableL 2 "i1")
expL_b = AddL 4 expL_a (VariableL 5 "i2")

-- The multiplication example reads as follows.
-- The function mulL takes an extra argument, the initial label counter, 
-- and returns the final counter as the extra result.

mulL :: Int -> ExpL -> Lab -> (Lab,ExpL)
mulL 0 _ p = (p+1, ConstantL p 0)
mulL 1 x p = (p,x)
mulL n x p | n `mod` 2 == 0 = mulL (n `div` 2) (AddL p x x) (p+1)
mulL n x p = let (p',r) = mulL (n-1) x p in (p'+1, AddL p' x r)

-- Last-but-one line shows a crucial point: two children of AddL
-- will have the same label
expL_mul4 = mulL 4 (VariableL 0 "i1") 1
{-
(3,AddL 2 (AddL 1 (VariableL 0 "i1") (VariableL 0 "i1"))
          (AddL 1 (VariableL 0 "i1") (VariableL 0 "i1")))
-}

expL_mul8 = mulL 8 (VariableL 0 "i1") 1

{-
(4,
  AddL 3 
   (AddL 2 
      (AddL 1 (VariableL 0 "i1") (VariableL 0 "i1")) 
      (AddL 1 (VariableL 0 "i1") (VariableL 0 "i1"))) 
   (AddL 2 
     (AddL 1 (VariableL 0 "i1") (VariableL 0 "i1")) 
     (AddL 1 (VariableL 0 "i1") (VariableL 0 "i1"))))
-}


-- Approach 2: use the state monad to automate label assignment.
-- The state monad was already apparent in the implementation of mulL

type ExpM = State Lab ExpL

new_labelM :: State Lab Lab
new_labelM = do
  p <- get
  put (p+1)
  return p

-- `smart constructors' to construct expressions,
-- obtaining the fresh label
varM :: String -> ExpM
varM v   = new_labelM >>= \p -> return $ VariableL p v

constM :: Int -> ExpM
constM x = new_labelM >>= \p -> return $ ConstantL p x

addM :: ExpL -> ExpL -> ExpM
addM x y = new_labelM >>= \p -> return $ AddL p x y

{-
-- Exercise: what is the problem with the following definition?

addM :: ExpM -> ExpM -> ExpM
addM x y = do
  xv <- x
  yv <- y
  l  <- new_labelM
  return $ AddL l xv yv

expM_a = addM (constM 10) (varM "i1")
-}

run_expM :: ExpM -> ExpL
run_expM m = evalState m 0

-- The running examples
{- O'Donnell wrote (cited from Alfonso Acosta's thesis):
``A more severe problem is that the circuit specification is no longer
a system of simultaneous equations, which can be manipulated formally
just by 'substituting equals for equals'. Instead, the specification
is now a sequence of computations that --when executed-- will yield
the desired circuit. It feels like writing an imperative program to
draw a circuit, instead of defining the circuit directly."[33]''
-}

expM_a = do 
         xv <- constM 10 
         yv <- varM "i1"
         addM xv yv

expM_b = do 
         xv <- expM_a
         yv <- varM "i2"
         addM xv yv
{-
*Ptrs> run_expM expM_b
AddL 4 (AddL 2 (ConstantL 0 10) (VariableL 1 "i1")) (VariableL 3 "i2")
-}


-- The monadic notation simplifies mulL, hiding the label counter
-- manipulation
-- (=<<) as a call-by-value application
mulM :: Int -> ExpL -> ExpM
mulM 0 _ = constM 0
mulM 1 x = return x
mulM n x | n `mod` 2 == 0 = mulM (n `div` 2) =<< addM x x
mulM n x = addM x =<< mulM (n-1) x

-- Last-but-one line shows a crucial point: two children of AddL
-- will have the same label
expM_mul4 = mulM 4 =<< (varM "i1")

{-
*Ptrs> run_expM expM_mul4
AddL 2 
  (AddL 1 (VariableL 0 "i1") (VariableL 0 "i1")) 
  (AddL 1 (VariableL 0 "i1") (VariableL 0 "i1"))
-}


-- Approach 3: observable sharing
-- The other approach: see Naylor (LavaUnsafe)

-- Why do we need NOINLINE?
{-# NOINLINE counter #-}
counter = unsafePerformIO (newIORef 0)


-- gensym, essentially
new_label :: () -> Int
new_label () = unsafePerformIO $ do
  p <- readIORef counter
  writeIORef counter (p+1)
  return p


varU :: String -> ExpL
varU v = VariableL (new_label ()) v

constU :: Int -> ExpL
constU x = ConstantL (new_label ()) x

-- Apparently a pure type
addU :: ExpL -> ExpL -> ExpL
addU x y = AddL (new_label ()) x y

-- Why can't we eta-reduce the definitions?
-- constU = ConstantL (new_label ())
-- varU = VariableL (new_label ())
-- addU = AddL (new_label ())

-- This is the price of lying to the compiler

-- Sample expression
expU_a = addU (constU 10) (varU "i1")
-- AddL 0 (ConstantL 1 10) (VariableL 2 "i1")

expU_b = addU expU_a (varU "i2")
-- AddL 3 (AddL 0 (ConstantL 1 10) (VariableL 2 "i1")) (VariableL 4 "i2")

-- The attraction: pure type, pure applications
mulU :: Int -> ExpL -> ExpL
mulU 0 _ = constU 0
mulU 1 x = x
mulU n x | n `mod` 2 == 0 = mulU (n `div` 2) (addU x x)
mulU n x = addU x (mulU (n-1) x)

-- Equal expressions got equal labels
expU_mul4 = mulU 4 (varU "i1")
{-
AddL 0 (AddL 1 (VariableL 2 "i1") (VariableL 2 "i1")) 
       (AddL 1 (VariableL 2 "i1") (VariableL 2 "i1"))
-}

expU_mul8 = mulU 8 (varU "i1")
{-
AddL 3 
  (AddL 4 (AddL 5 (VariableL 6 "i1") (VariableL 6 "i1")) 
          (AddL 5 (VariableL 6 "i1") (VariableL 6 "i1")))
  (AddL 4 (AddL 5 (VariableL 6 "i1") (VariableL 6 "i1")) 
          (AddL 5 (VariableL 6 "i1") (VariableL 6 "i1")))
-}




main = do
       print expL_mul8
       print $ run_expM expM_mul4
       print $ expU_b
       print expU_mul8

