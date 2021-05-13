import Parse
import Data.Char (isUpper)

{-
Rough encoding of Lambda-Mu Calculus from the paper:
{lambda-mu}-CALCULUS: AN ALGORITHMIC INTERPRETATION OF CLASSICAL NATURAL DEDUCTION

Examples of use at the bottom of this file



Symmetric Lambda Calculus expands on this stuff with continuations giving classical logic.

"|" used instead of lambda
"u" used instead of mu


uA.blah , all [A]e in blah are named and (uA.blah w) reduces to uA.blah with all named terms having w added as an argument ie. [A]e -> [A](e w)
if you name a mu, [A]uB.e, this means A names all terms named B in e (renaming rule implements this)

You can see mu variables as naming subterms and allowing operations to be applied to them
Mu variables refer to continuations and the above corresponds
to the shift from applying an operation to a value send to a particular continuation to applying the operation before the value is send to that continuation

In programming terminology:
u[B].e captures the current continuation and stores it in B then computes e.
[B]e overrides the current continuation with B and continues computing e, or if you prefer sends the value e to the continuation B.


The new constructs allow the manipulation of continuations and give a type system with the rules of classical logic.
The reduction rules may not make this clear as they allow for flexiblity in the reduction order while allways giving the same result (confluence).
To preserve this flexibility, rules are not given for things like (w uA.blah),
even though in practical programming languages with continuation manipulation would have the rule.



Uses nat deduction with multiple output, there is a active output (corresponds to the current continuation) and the others are indexed by mu variables (stored in variables).


--below is a paraphrasing of a comment from the paper, can I connect to a form of CPS?
--CPS allows for delimited continuations, i think lambda-mu only allows capture and replacing of the whole current continuation (as does SLC, it seems classical logic needs this?)
In lambda-mu some terms give the same result regardless of the number of arguments it is applied to,
this means a mu looks like a lambda with potentialy infinitely many arguments
In the case where the number of arguments are known ahead of time, mu can be replaced with lambda with n arguments and named terms by the term applied to the n arguments.

-}

--I assume distinct bound and free variables, and each bound variable is bound once. This is to avoid handling name conflicts.


--have a general replace that takes function which can reject? This might not allow for handling of shadowing etc.



data Term = Var String | Abs Term Term | App Term Term | MuVar String | Mu Term Term | Brack Term Term deriving (Eq, Show)



--usual beta reduction (called logical reduction in lambda-mu) - replaces all terms x in u with v
reduce1 (App (Abs x@(Var _) u) v) = replace v x u
--structural reduction - replaces all terms named b in u with the named term applied to v
reduce1 (App (Mu b@(MuVar _) u) v) = Mu b $ mureplace v b u
--renaming - replace all a in u with b
reduce1 (Brack a (Mu b@(MuVar _) u)) = replace a b u

--for convenience
reduce1 (Abs x e) = Abs x (reduce1 e)
reduce1 (Mu q w) = Mu q (reduce1 w)
reduce1 (Brack a b) = Brack a (reduce1 b)

reduce1 (App a b) = App (reduce1 a) b

reduce1 t@(Var _) = t
reduce1 t@(MuVar _) = t


--has flaws (does not reduce right side of App)
reducen v | r==v = r
          | otherwise = reducen r
        where r = reduce1 v

--can make the replaces nicer, unify them for one
--as mentioned at the top, shadowing etc. is ignored

--something like this is smaller
--replace a x v | x==v = a -- + cases for var shadowing
--              | otherwise = fmap (replace a x) v--of course not fmap itself
replace a x y@(Var _) | x==y = a
                      | otherwise = y--main 1
replace a x (Abs y e) = Abs y (replace a x e)
replace a x (App q w) = App (replace a x q) (replace a x w)
replace a x y@(MuVar _) | x==y = a
                        | otherwise = y--main 2
replace a x (Mu y e) = Mu y (replace a x e)
replace a x (Brack q w) = Brack (replace a x q) (replace a x w)

--replace replaces variables with a term
--mureplace(bad name) adds an arguments to named terms (replaces the named term with itself applied to something)
mureplace a x y@(Var _) = y
mureplace a x (Abs y e) = Abs y (mureplace a x e)
mureplace a x (App q w) = App (mureplace a x q) (mureplace a x w)
mureplace a x y@(MuVar _) = y
mureplace a x (Mu y e) = Mu y (mureplace a x e)

mureplace a x (Brack q w)| x==q = Brack q (App w a)--main
                         | otherwise = Brack q (mureplace a x w)



nicefy f str = prettyPrint $ f $ maybe (error "failed to parse") id $ readTerm str
niceReduce1 = nicefy reduce1
niceReducen = nicefy reducen

----Printer
--does not remove unnecessary brackets
prettyPrint (Var a)     = a
prettyPrint (Abs a b)   = "|" ++ prettyPrint a ++ "." ++ prettyPrint b
prettyPrint (App a b)   = "(" ++ prettyPrint a ++ " " ++ prettyPrint b ++ ")"
prettyPrint (MuVar a)   = a
prettyPrint (Mu a b)    = "u" ++ prettyPrint a ++ "." ++ prettyPrint b
prettyPrint (Brack a b) = "[" ++ prettyPrint a ++ "]" ++ prettyPrint b


----Parser
{-
Parser is a bit strict,
can give non standard results eg.
readTerm "(|x.x y)" => App (Abs (Var "x") (Var  "x")) (Var "y") instead of Abs (Var "x") (App (Var "x") (Var "y"))
but I want a general method of handling precedence etc. rather than duplicating effort of manually doing it from my other programs
-}

-- "|" is used instead of lambda
-- lowercase symbols are read as Var upcase as MuVar
readTerm str = parse termExpr str
termExpr = orP absExpr $ orP appExpr $ orP muExpr $ orP brackExpr mvarExpr
absExpr = apply (\(a,b) -> Abs a b)   $ seqPairR (word "|") $ seqPair mvarExpr $ seqPairR (word ".") termExpr
appExpr = apply (\(a,b) -> App a b)   $ seqPairR (word "(") $ seqPair termExpr $ seqPairR (word " ") $ seqPairL termExpr (word ")")
muExpr  = apply (\(a,b) -> Mu a b )   $ seqPairR (word "u") $ seqPair mvarExpr $ seqPairR (word ".") termExpr
brackExpr=apply (\(a,b) -> Brack a b) $ seqPairR (word "[") $ seqPair termExpr $ seqPairR (word "]") termExpr
mvarExpr = apply (\a -> if and $ map isUpper a then MuVar a else Var a) $ oneOrMore varChar
      where varChar = foldr1 orP $ map (\a -> char a a) $ ['a'..'z'] ++ ['A'..'Z']


----Examples/Tests

t1 = niceReducen "(|x.x y)" -- => "y"
t2 = niceReducen "(uX.(u [X]v) a)" -- => "uX.(u [X](v a))"
t3 = niceReducen "[Y]uX.([X]u v)" -- => "([Y]u v)"
