{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}

-- Embedding Domain-specific languages in pure Haskell
-- and the explicit representation of sharing. The tagless final approach.
-- This file is based on the original code posted on 
-- Haskell-Cafe in February 2008.
-- For more recent and detailed version, see
--      http://okmij.org/ftp/tagless-final/sharing/


module DSLSharing where

{-
Tom Hawkins  wrote:
 in http://www.haskell.org/pipermail/haskell-cafe/2008-February/039339.html
<blockquote>
 My DSLs invariably define a datatype to capture expressions; something
 like this:

 data Expression
   = Add Expression Expression
   | Sub Expression Expression
   | Variable String
   | Constant Int
   deriving Eq
 The problem comes when I want to generate efficient code from an
 Expression (ie. to C or some other target language).  The method I use
 involves converting the tree of subexpressions into an acyclic graphic
 to eliminate common subexpressions.  The nodes are then topologically
 ordered and assigned an instruction, or statement for each node.  For
 example:

 let a = Add (Constant 10) (Variable "i1")
     b = Sub (Variable "i2") (Constant 2)
     c = Add a b
 The process of converting an expression tree to a graph uses either Eq
 or Ord (either derived or a custom instance) to search and build a set
 of unique nodes to be ordered for execution.  In this case "a", then
 "b", then "c".  The problem is expressions often have shared,
 equivalent subnodes, which dramatically grows the size of the tree.
 For example:

 let d = Add c c
     e = Add d d    -- "e" now as 16 leaf nodes.

 As these trees grow in size, the equality comparison in graph
 construction quickly becomes the bottleneck for DSL compilation.
What's worse, the phase transition from tractable to intractable is
very sharp.  In one of my DSL programs, I made a seemingly small
change, and compilation time went from milliseconds to
not-in-a-million-years.

Is there anything that can be done to dramatically speed up
comparisons, or is there a better approach I can take to extract
common subexpressions?  I should point out I have an opportunity to
get Haskell on a real industrial application.  But if I can't solve
this problem, I may have to resort to far less eloquent languages.
:-(
</blockquote>

We show the design of the same sort of DSL that explicitly maintains
sharing information and where node comparisons are quick, because we
are comparing hashes rather than trees themselves. Our approach is
assuredly safe, pure, and Haskell98 (save for disabling of the
monomorphism restriction, which is done solely to avoid writing
signatures). No GHC-specific behavior is relied upon.

Our DSL has a form (let_) to let a DSL programmer declare sharing of
the _results_ of DSL computations (rather than computations
themselves). The programmer may thus state their intention that a
computation to be considered `common', be executed once and their
result be shared. The programmer thus greatly helps the compiler as
well as human readers of the code.


Other relevant message:

Matthew Naylor
http://www.haskell.org/pipermail/haskell-cafe/2008-February/039347.html
http://www.haskell.org/pipermail/haskell-cafe/2008-February/039449.html

http://www.haskell.org/pipermail/haskell-cafe/2008-February/039566.html
http://www.haskell.org/pipermail/haskell-cafe/2008-February/039575.html
http://www.haskell.org/pipermail/haskell-cafe/2008-February/039577.html

Chung-chieh Shan
http://www.haskell.org/pipermail/haskell-cafe/2008-February/039554.html

David Menendez
http://www.haskell.org/pipermail/haskell-cafe/2008-February/039594.html

sklansky:
http://www.haskell.org/pipermail/haskell-cafe/2008-February/039671.html
http://www.haskell.org/pipermail/haskell-cafe/2008-February/039737.html
-}


import Data.IntMap as IM
import Control.Monad.State hiding (ap)

-- The approach is based on the final tagless representation. Here is our
-- DSL:

class Exp repr where
   constant :: Int -> repr Int
   variable :: String -> repr Int
   add  :: repr Int -> repr Int -> repr Int
   sub  :: repr Int -> repr Int -> repr Int
   let_ :: repr a -> (repr a -> repr b) -> repr b 
   let_ x f = f x                -- default is the reverse application

-- Our expressions here are of only one type, Int. We could have dropped
-- Int and made 'repr' to be a type variable of the kind *.
-- We keep the 'repr Int' notation nevertheless, for consistency
-- with the tagless final paper, and to allow for extensions (e.g.,
-- addition of booleans). This point is well made by David Menendez,
-- op cit.
-- ``The argument to repr prevents you from writing ill-typed code like
-- "if_ (variable "x") (constant 0) false".''

-- Tom Hawkins' test expressions (quoted in the title comments)
-- now look as follows

a = add (constant 10) (variable "i1")
b = sub (variable "i2") (constant 2)
c = add a b
d = add c c
e = add d d    -- "e" now as 16 leaf nodes.
e' = let_ d (\x -> add x x)

-- which is the same as before modulo the case of the identifiers:
-- everything is in lower case.


-- We can show the expressions as before: showing is one way
-- of evaluating things

type LetVarCount = Int                        -- counter for generating let-var-names
newtype S t = S{unS :: LetVarCount -> String}

instance Exp S where
    constant  = S . const . show
    variable  = S . const
    add e1 e2 = S(\c -> unS e1 c ++ " + " ++ unS e2 c)
    sub e1 e2 = S(\c -> unS e1 c ++ " - " ++ unS e2 c)
    let_ e f  = S(\c -> let vname = "v" ++ show c
                        in unwords ["let",vname,"=",unS e c,
                                    "in",unS (f (S (const vname))) (succ c)])

-- We can see the difference in what is shared in DSL programs (e) and
-- (e'). The program (e) uses the identifier (d) twice; even if
-- GHC shares the corresponding expressions rather than copies them (a
-- Haskell system is not obliged to share anything: sharing is not
-- observable in Haskell98), what GHC shares are metalanguage
-- computations. Although the metalanguage (Haskell) is pure, the object
-- language does not have to be. Indeed, the common-subexpression
-- elimination (see evaluator A below), when considered as an
-- evaluation of an object expression, is an impure evaluation.
-- The same object expression may give, in different contexts, different
-- results (that is, compile to different assembly code). 
-- In the case of (e'), we explicitly stated that "d" is a common
-- sub-expression. It must be executed once, with the results shared.

test_showe = unS e 0

{-
 *DSLSharing> test_showe
 "10 + i1 + i2 - 2 + 10 + i1 + i2 - 2 + 10 + i1 + i2 - 2 + 10 + i1 + i2 - 2"
-}

test_showe' = unS e' 0
{-
 *DSLSharing> test_showe'
 "let v0 = 10 + i1 + i2 - 2 + 10 + i1 + i2 - 2 in v0 + v0"
-}



-- We can write an evaluator for the expressions
type REnv = [(String,Int)]
newtype R t = R{unR :: REnv -> t} -- A reader Monad, actually

instance Exp R where
    constant x = R $ const x
    variable x = R ( \env -> maybe (error $ "no var: " ++ x) id $ 
                     Prelude.lookup x env)
    add e1 e2 = R(\env -> unR e1 env + unR e2 env)
    sub e1 e2 = R(\env -> unR e1 env - unR e2 env)


test_vale = unR e [("i1",5),("i2",10)] -- 92
-- We stress: we are using exactly the same expression e as before. 
-- We are only evaluating it differently. The gist of the final tagless
-- approach is to write an expression once and evaluate it many times.

test_vale' = unR e' [("i1",5),("i2",10)] -- 92


-- Now, we chose a different representation: to make sharing explicit
-- We chose not to rely on GHC; we don't care if in (add c c), the two
-- c are shared or copied. It is not observable in pure Haskell,
-- and we don't care. We build our acyclic graph nevertheless.

type ExpHash = Int

-- We stress: ACode is NOT a recursive data structure, so the comparison
-- of ACode values takes constant time!
data ACode = AConst ExpHash |
             AVar   ExpHash |
             AAdd   ExpHash |
             ASub   ExpHash
             deriving (Eq,Show)

data ExpMaps = ExpMaps{ hashcnt :: ExpHash, -- to generate new Hash
                        ctmap :: IntMap Int,
                        vrmap :: IntMap String,
                        admap :: IntMap (ACode,ACode),
                        sumap :: IntMap (ACode,ACode)}
             deriving Show
exmap0 = ExpMaps 0 IM.empty IM.empty IM.empty IM.empty


newtype A t = A{unA :: State ExpMaps ACode}


-- Granted, the following could be done far more efficiently: we need
-- bimaps.

loookupv :: Eq v => v -> IntMap v -> Maybe Int
loookupv v = IM.foldrWithKey
             (\k e z -> maybe (if e == v then Just k else Nothing) (const z) z)
             Nothing


record con prj upd x = do
  s <- get
  maybe (do let s' = upd (s{hashcnt = succ (hashcnt s)})
                         (IM.insert (hashcnt s) x (prj s))
            put s'
            -- trace "updating map" (return ())
            return (con $ hashcnt s))
        (return . con) $ loookupv x (prj s)

instance Exp A where
    constant x = A(record AConst ctmap (\s e -> s{ctmap = e}) x)
    variable x = A(record AVar vrmap (\s e -> s{vrmap = e}) x)
    add e1 e2  = A(do
                   h1 <- unA e1
                   h2 <- unA e2
                   record AAdd admap (\s e -> s{admap = e}) (h1,h2))
    sub e1 e2  = A(do
                   h1 <- unA e1
                   h2 <- unA e2
                   record ASub sumap (\s e -> s{sumap = e}) (h1,h2))

    let_ e f = A(do
                 x <- unA e
                 unA $ f (A (return x)))

-- Again, we are using the very same expression e we wrote at the very
-- beginning:

test_sme = runState (unA e) exmap0

{-
*DSL> test_sme
(AAdd 8,
  ExpMaps {hashcnt = 9, 
    ctmap = fromList [(0,10),(4,2)], 
    vrmap = fromList [(1,"i1"),(3,"i2")], 
    admap = fromList [(2,(AConst 0,AVar 1)),(6,(AAdd 2,ASub 5)),
                      (7,(AAdd 6,AAdd 6)),(8,(AAdd 7,AAdd 7))], 
    sumap = fromList [(5,(AVar 3,AConst 4))]})

We retain all the information about expression 'e'. In addition, all
sharing is fully explicit. As we can see, the evaluation process finds
common subexpressions automatically.
-}

{-
Matthew Naylor's original tricky example
``Also, my mental model is big circuits'' [Matthew Naylor]

Sharing is expressed in the meta-language rather than in the object language.
Here, sharing makes it easier for a metalanguage system to build
an object language program. The object language program has no 
explicit sharing however, and therefore, the program is huge.
Our common-subexpression eliminator, evaluator A above,
can significantly condense it, to a linear DAG, as shown below. 
Alas, to find all these common subexpressions and eliminate them, 
our A evaluator has to examine all the nodes of the object program, 
all 2^(d+1)-1 of them.
-}

tricky 0 = constant 0
tricky d = add g g
    where
      g = tricky (d-1)

test_tricky n = runState (unA (tricky n)) exmap0

{-
 *DSLSharing> test_tricky 12
 (AAdd 12,
   ExpMaps {hashcnt = 13, ctmap = fromList [(0,0)], vrmap = fromList [], 
   admap = 
    fromList [(1,(AConst 0,AConst 0)),(2,(AAdd 1,AAdd 1)),
              (3,(AAdd 2,AAdd 2)),(4,(AAdd 3,AAdd 3)),(5,(AAdd 4,AAdd 4)),
              (6,(AAdd 5,AAdd 5)),(7,(AAdd 6,AAdd 6)),(8,(AAdd 7,AAdd 7)),
              (9,(AAdd 8,AAdd 8)),(10,(AAdd 9,AAdd 9)),(11,(AAdd 10,AAdd 10)),
              (12,(AAdd 11,AAdd 11))], sumap = fromList []})
(0.25 secs, 10659560 bytes)

test_tricky 10 takes (0.06 secs, 3488240 bytes)
test_tricky 11 takes (0.12 secs, 5495480 bytes)
-}

-- We re-write the tricky function with the explicit sharing:

tricky' 0 = constant 0
tricky' d = let_ (tricky' (d-1)) (\g -> add g g)

test_tricky' n = runState (unA (tricky' n)) exmap0

{-
 *DSLSharing> test_tricky' 12
 (AAdd 12,
   ExpMaps {hashcnt = 13, ctmap = fromList [(0,0)], vrmap = fromList [],
   admap = 
    fromList [(1,(AConst 0,AConst 0)),(2,(AAdd 1,AAdd 1)),
              (3,(AAdd 2,AAdd 2)),(4,(AAdd 3,AAdd 3)),(5,(AAdd 4,AAdd 4)),
              (6,(AAdd 5,AAdd 5)),(7,(AAdd 6,AAdd 6)),(8,(AAdd 7,AAdd 7)),
              (9,(AAdd 8,AAdd 8)),(10,(AAdd 9,AAdd 9)),(11,(AAdd 10,AAdd 10)),
              (12,(AAdd 11,AAdd 11))], sumap = fromList []})
(0.01 secs, 0 bytes)

test_tricky' 12 takes (0.01 secs, 561860 bytes)
test_tricky' 100 takes (0.03 secs, 1444888 bytes)

If the DAG corresponding to (test_tricky' 100) were converted to a
tree, it would have had 2^101 -1 nodes (which is more than 10^31).

-}

-- We now show two examples with explicit sharing and implicit sharing.
-- The implicit sharing is left for our common sub-expression eliminator
-- to discover.

-- In this example, we `join' two tricky trees using a meta-level `let'.
-- The sharing is implicit and is not stated in the object language.
tricky2 n = let d = tricky' n in sub d d
test_tricky2 n = runState (unA (tricky2 n)) exmap0

{-
 *DSLSharing> test_tricky2 10
 (ASub 11,
   ExpMaps {hashcnt = 12, ctmap = fromList [(0,0)], vrmap = fromList [], 
    admap = 
     fromList [(1,(AConst 0,AConst 0)),(2,(AAdd 1,AAdd 1)),
               (3,(AAdd 2,AAdd 2)),(4,(AAdd 3,AAdd 3)),(5,(AAdd 4,AAdd 4)),
               (6,(AAdd 5,AAdd 5)),(7,(AAdd 6,AAdd 6)),(8,(AAdd 7,AAdd 7)),
               (9,(AAdd 8,AAdd 8)),(10,(AAdd 9,AAdd 9))], 
    sumap = fromList [(11,(AAdd 10,AAdd 10))]})
(0.01 secs, 0 bytes)

test_tricky2 100 takes (0.06 secs, 2508896 bytes)
The implicit sharing is discovered.
-}

-- A different example that deliberately includes common sub-expressions.
-- Sharing is not stated even in the meta-language.
tricky'' 0 = constant 0
tricky'' d = let_ (tricky'' (d-1)) (\g -> sub (add g g) (add g g))

test_tricky'' n = runState (unA (tricky'' n)) exmap0

{-
*DSLSharing> test_tricky'' 10
  (ASub 20,
   ExpMaps {hashcnt = 21, ctmap = fromList [(0,0)], vrmap = fromList [], 
    admap = 
     fromList [(1,(AConst 0,AConst 0)),(3,(ASub 2,ASub 2)),
               (5,(ASub 4,ASub 4)),(7,(ASub 6,ASub 6)),(9,(ASub 8,ASub 8)),
               (11,(ASub 10,ASub 10)),(13,(ASub 12,ASub 12)),
               (15,(ASub 14,ASub 14)),(17,(ASub 16,ASub 16)),
               (19,(ASub 18,ASub 18))],
    sumap = 
     fromList [(2,(AAdd 1,AAdd 1)),(4,(AAdd 3,AAdd 3)),(6,(AAdd 5,AAdd 5)),
               (8,(AAdd 7,AAdd 7)),(10,(AAdd 9,AAdd 9)),(12,(AAdd 11,AAdd 11)),
               (14,(AAdd 13,AAdd 13)),(16,(AAdd 15,AAdd 15)),
               (18,(AAdd 17,AAdd 17)),(20,(AAdd 19,AAdd 19))]})
(0.02 secs, 1614424 bytes)

test_tricky'' 100 takes (0.08 secs, 4726648 bytes)
-}


-- sklansky example by Matthew Naylor, with further credit to
-- Chalmers folk, Mary Sheeran and Emil Axelsson.
-- It is said to be similar to scanl1, but contains more parallelism

{- The original code, from Matthew Naylor's message:
  http://www.haskell.org/pipermail/haskell-cafe/2008-February/039671.html
-}

sklansky :: (a -> a -> a) -> [a] -> [a]
sklansky f [] = []
sklansky f [x] = [x]
sklansky f xs = left' ++ [ f (last left') r | r <- right' ]
   where
     (left, right) = splitAt (length xs `div` 2) xs
     left'  = sklansky f left
     right' = sklansky f right

test_sklansky_o n = sklansky addition xs
   where
     addition x y = "(" ++ x ++ "+" ++ y ++ ")"
     xs = Prelude.map (("v"++) . show) [1..n]

-- (v1+v2) is used three times
{-
test_sklansky_o 4
["v1","(v1+v2)","((v1+v2)+v3)","((v1+v2)+(v3+v4))"]
-}

-- (v1+v2) is used seven times
{-
test_sklansky_o 8
["v1","(v1+v2)",
 "((v1+v2)+v3)",
 "((v1+v2)+(v3+v4))",
 "(((v1+v2)+(v3+v4))+v5)",
 "(((v1+v2)+(v3+v4))+(v5+v6))",
 "(((v1+v2)+(v3+v4))+((v5+v6)+v7))",
 "(((v1+v2)+(v3+v4))+((v5+v6)+(v7+v8)))"]
-}

-- We re-write in the tagless-final style
-- Actually, there is no re-write
-- We use Matthew Naylor's code, in pure Haskell, as it was

-- We run it differently though

test_sklansky n = runState sk exmap0
   where
     sk = sequence (Prelude.map unA (sklansky add xs))
     xs = Prelude.map (variable . show) [1..n]

-- Implicit sharing works: AAdd 2 is used three times
{-
*DSLSharing> test_sklansky 4
([AVar 0,AAdd 2,AAdd 4,AAdd 7],
 ExpMaps {hashcnt = 8, ctmap = fromList [], 
 vrmap = fromList [(0,"1"),(1,"2"),(3,"3"),(5,"4")], 
 admap = fromList [(2,(AVar 0,AVar 1)),
                   (4,(AAdd 2,AVar 3)),
                   (6,(AVar 3,AVar 5)),
                   (7,(AAdd 2,AAdd 6))], sumap = fromList []})
-}

-- We see deep sharing: AAdd 2, which is v1+v2 is used twice.
-- Then AAdd 7, which is (v1+v2)+(v3+v4), is used 4 times
-- after being computed
{-
*DSLSharing> test_sklansky 8
([AVar 0,AAdd 2,AAdd 4,AAdd 7,AAdd 9,AAdd 12,AAdd 15,AAdd 19],
  ExpMaps {hashcnt = 20, ctmap = fromList [], 
  vrmap = fromList 
    [(0,"1"),(1,"2"),(3,"3"),(5,"4"),(8,"5"),(10,"6"),(13,"7"),(16,"8")], 
  admap = fromList 
  [(2,(AVar 0,AVar 1)),
   (4,(AAdd 2,AVar 3)),
   (6,(AVar 3,AVar 5)),
   (7,(AAdd 2,AAdd 6)),
   (9,(AAdd 7,AVar 8)),
   (11,(AVar 8,AVar 10)),
   (12,(AAdd 7,AAdd 11)),
   (14,(AAdd 11,AVar 13)),
   (15,(AAdd 7,AAdd 14)),
   (17,(AVar 13,AVar 16)),
   (18,(AAdd 11,AAdd 17)),
   (19,(AAdd 7,AAdd 18))], sumap = fromList []})
-}

-- test_sklansky 128
-- Surprisingly, it is quite fast...
-- Although slowness is noticeable.

let_many :: Exp repr => [repr a] -> ([repr a] -> repr b) -> repr b
let_many bs f = let_many' bs [] f
 where
 let_many' [] acc f = f (reverse acc)
 let_many' (b:bs) acc f = let_ b (\b -> let_many' bs (b:acc) f)

-- See ExpLetList.hs for a better solution.
