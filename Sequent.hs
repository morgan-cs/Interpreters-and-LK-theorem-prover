import Parse


{-
A classical propositional theorem prover giving proofs in LK sequent calculus.

niceProveProp is the most useful function. 
example:
> niceProveProp "((a->b)->c)->b->c"
Root _ |- ((a -> b) -> c) -> b -> c
ImplyR (a -> b) -> c |- b -> c
ImplyL _ |- a -> b,b -> c
         ImplyR a |- b,b -> c
         ImplyR b,a |- c,b
         Axiom
       c |- b -> c
         ImplyR b,c |- c
         Axiom
> niceProveProp "(a^b -> c)^(d -> a^f) -> (b^d -> c^f)"

Possible improvements:

Get Unicode working in the repl so I can use better symbols such as "¬" instead of "-"
Move from String to Text where appropriate.

Extend to first order logic (semi-decidable in general, decidable given no function symbols and arity 1 predicatets) (this may require getting unique new symbols)

Genralise the infix printing and parsing.

DONE:Change translation rule like ImplyL to directly split, to remove reliance on a different connectetive having a splitting rule. this also makes it cleaner to show the algorithm always terminates

Have explicit structural rules, instead of implicit rotation
or instead makes things more implicit, having early exits when equal atomics are spotted and so on.
this would give shorter more natural proofs, but may make modification to other logics harder. 
could implicitising be instead a second pass on the proof structure???

Find normal form of a proof.

Find shortest proof possible according to some measure. Allowing a database of theorems would be beneficial.
(might depend on how explicit structural rules are, if theres an early exit) (a breadth first search of all proofs should work, though of course inefficient)


DONE:Make a parser.
DONE:Visually display proof trees, since this only has binary trees text should be enough, other proof systems like cirquents would need some sort of graph

proof validator, to check a proof is correct. (and if its a proof, or a proof of falsity etc.)
The analog of type inference, finding the Prop that a proof proofs is trivial with the extra info I put in proofs.
Human proof verifier: decisions for how explicit to be, could suggest things to place in blank or non-explicit areas
-}

--could add reverse imply to complete the duality (<-)
data Prop = Name String | And Prop Prop | Or Prop Prop | Imply Prop Prop | Not Prop deriving (Eq)

bracketfy s = "(" ++ s ++ ")"
-- Caller determines if there are brackets around and expression
-- I'm using this precedence/strength of binding
-- "Name" > "-" > "^" > "+" > "->"
-- Using "-" and "+" as I can't get Unicode to work in the haskell repl

--would be better to not override the default show as its output can be read back in by haskell
--remove some of the space around some operators? paricularly ^ and +
instance Show Prop where
  show (Name a) = a
  show (And a b) = a2 ++ " ^ " ++ b2
                  where a2 = case a of
                               Imply _ _ -> bracketfy $ show a
                               Or _ _ -> bracketfy $ show a
                               And _ _ -> show a --bc associative
                               otherwise -> show a
                        b2 = case b of
                               Imply _ _ -> bracketfy $ show b
                               Or _ _ -> bracketfy $ show b
                               And _ _ -> show b --bc associative
                               otherwise -> show b
  show (Or a b) = a2 ++ " + " ++ b2
                  where a2 = case a of
                               Imply _ _ -> bracketfy $ show a
                               Or _ _ -> show a --bc associative
                               otherwise -> show a
                        b2 = case b of
                               Imply _ _ -> bracketfy $ show b
                               Or _ _ -> show b --bc associative
                               otherwise -> show b
  show (Imply a b) = a2 ++ " -> " ++ b2
                  where a2 = case a of
                               Imply _ _ -> bracketfy $ show a--bc right associative
                               otherwise -> show a
                        b2 = case b of
                               Imply _ _ -> show b --bc right associative
                               otherwise -> show b
  show (Not a) = "-" ++ (case a of
                           Name _ -> show a
                           Not _ -> show a
                           otherwise -> bracketfy $ show a)

{-
--How to capture the above pattern?
showInfix lAssoc precedence v = a ++ (showOperator v) ++ b
                            where a | lprecedence v < precedence v = bracketfy $ show lv
                                    | lprecedence v == precedence v = if lAssoc then (show lv) else (bracketfy $ show lv)
                                    | lprecedence v > precedence v = show lv
                                  b = 
-}

data Seq = Seq [Prop] [Prop] deriving (Eq, Show)

allAtomics (Seq l r) = and $ ((map f l) ++ (map f r))
               where f (Name _) = True
                     f a = False

--works on things other than atomics
isAxiom (Seq l r) = or $ map (\a -> member a r) l

rotate [] = []
rotate (x:xs) = xs ++ [x]
member x xs = or $ map (\a -> x==a) xs


--provePT defined below outputs proof

--using prove to figure out the core rules  without adding the extra distractions
--change to match structure provePT?
prove :: Seq -> Bool
-- should write the general forms of the rules to convince myself eg. a,S1 |- b->c,S2 <=> a,b,S1 |- S2
-- a -> (b -> c) <=> a ^ b -> c 
prove (Seq ((Imply a b):l) r) = and [prove $ Seq l (a:r), prove $ Seq (b:l) r]
prove (Seq l ((Imply a b):r)) = prove $ Seq (a:l) (b:r)


-- a+b -> c <=> (a -> c)^(b -> c)
prove (Seq ((Or a b):l) r) = and [(prove $ Seq (a:l) r), (prove $ Seq (b:l) r)]
prove (Seq l ((Or a b):r)) = prove $ Seq l (a:b:r)

prove (Seq ((And a b):l) r) = prove $ Seq (a:b:l) r
prove (Seq l ((And a b):r)) = and [(prove $ Seq (a:l) r), (prove $ Seq (b:l) r)]


prove (Seq ((Not a):l) r) = prove $ Seq l (a:r)
prove (Seq l ((Not a):r)) = prove $ Seq (a:l) r

--when all are atomics
prove s@(Seq l r) | allAtomics s = isAxiom s
                  | otherwise = prove $ Seq (rotate l) (rotate r)

--Placing the intermidiate state of the sequent in each step of the proof
data Proof = Root Seq Proof | Axiom | NonAxiom |
             ImplyL Seq Proof Seq Proof | ImplyR Seq Proof | 
             OrL Seq Proof Seq Proof | OrR Seq Proof | 
             AndL Seq Proof | AndR Seq Proof Seq Proof | 
             NotL Seq Proof | NotR Seq Proof deriving (Eq, Show)

provePT :: Seq -> Proof
provePT s = Root s (proveP s) --just so I can include the thing we are proving

proveP :: Seq -> Proof
proveP s | isAxiom s = Axiom
         | allAtomics s = NonAxiom --since isAxiom failed
         | otherwise = applyRule s

applyRule (Seq ((Imply a b):l) r) = ImplyL s1 (proveP s1) s2 (proveP s2)
                        where s1 = Seq l (a:r)
                              s2 = Seq (b:l) r
applyRule (Seq l ((Imply a b):r)) = ImplyR s2 (proveP s2)
                           where s2 = Seq (a:l) (b:r)

applyRule (Seq ((Or a b):l) r) = OrL s1 (proveP s1) s2 (proveP s2)
                        where s1 = Seq (a:l) r
                              s2 = Seq (b:l) r
applyRule (Seq l ((Or a b):r)) = OrR s2 (proveP s2)
                        where s2 = Seq l (a:b:r)

applyRule (Seq ((And a b):l) r) = AndL s2 (proveP s2)
                        where s2 = Seq (a:b:l) r

applyRule (Seq l ((And a b):r)) = AndR s1 (proveP s1) s2 (proveP s2)
                        where s1 = Seq l (a:r)
                              s2 = Seq l (b:r)

applyRule (Seq ((Not a):l) r) = NotL s2 (proveP s2)
                        where s2 = Seq l (a:r)
applyRule (Seq l ((Not a):r)) = NotR s2 (proveP s2)
                        where s2 = Seq (a:l) r

applyRule (Seq l r) = applyRule $ Seq (rotate l) (rotate r) --since we know there is a non-atomic via the checks in proveP


----Printing
--can be generalised and made nicer, I think I saw a haskell paper about this sort of formating.

--line up the sequents for non indented lines?

indent n [] = []
indent n ('\n':xs) = "\n" ++ (take n $ repeat ' ') ++ indent n xs
indent n (x:xs) = x:(indent n xs)

prettyPrintSeq (Seq [] []) = "_" ++ " |- " ++ "_"
prettyPrintSeq (Seq [] r) = "_" ++ " |- " ++ (init $ tail $ show r) --init $ tail   removes square brackets from show of a list
prettyPrintSeq (Seq l []) = (init $ tail $ show l) ++ " |- " ++ "_"
prettyPrintSeq (Seq l r) = (init $ tail $ show l) ++ " |- " ++ (init $ tail $ show r)

prettyPrintProof (Root s p) = "Root " ++ prettyPrintSeq s ++ ("\n" ++ prettyPrintProof p)
prettyPrintProof Axiom = "Axiom"
prettyPrintProof NonAxiom = "NonAxiom"

prettyPrintProof (ImplyL s1 p1 s2 p2) = "ImplyL " ++                prettyPrintSeq s1  ++ (indent (7+2) $ "\n" ++ prettyPrintProof p1) ++
                                                (indent 7 $ "\n" ++ prettyPrintSeq s2) ++ (indent (7+2) $ "\n" ++ prettyPrintProof p2)
prettyPrintProof (ImplyR s p) = "ImplyR " ++ prettyPrintSeq s ++ ("\n" ++ prettyPrintProof p)

prettyPrintProof (OrL s1 p1 s2 p2) =   "OrL " ++                    prettyPrintSeq s1  ++ (indent (4+2) $ "\n" ++ prettyPrintProof p1) ++
                                                (indent 4 $ "\n" ++ prettyPrintSeq s2) ++ (indent (4+2) $ "\n" ++ prettyPrintProof p2)
prettyPrintProof (OrR s p) = "OrR " ++ prettyPrintSeq s ++ ("\n" ++ prettyPrintProof p)

prettyPrintProof (AndL s p) = "AndL " ++ prettyPrintSeq s ++ ("\n" ++ prettyPrintProof p)
prettyPrintProof (AndR s1 p1 s2 p2) = "AndR " ++                    prettyPrintSeq s1  ++ (indent (5+2) $ "\n" ++ prettyPrintProof p1) ++
                                                (indent 5 $ "\n" ++ prettyPrintSeq s2) ++ (indent (5+2) $ "\n" ++ prettyPrintProof p2)

prettyPrintProof (NotL s p) = "NotL " ++ prettyPrintSeq s ++ ("\n" ++ prettyPrintProof p)
prettyPrintProof (NotR s p) = "NotR " ++ prettyPrintSeq s ++ ("\n" ++ prettyPrintProof p)


pProve = putStrLn . prettyPrintProof . provePT
niceProve = maybe (putStrLn "failed to parse") pProve . parseSequent
niceProveProp = maybe (putStrLn "failed to parse") pProve . fmap (\x -> Seq [] [x]) . parseProp


--Parsing
--generalise order of precidence stuff
--upgrade parser

parseSequent :: String -> Maybe Seq
parseSequent str = parse sequentExpr str

parseProp str = parse propExpr str

sequentExpr = apply (\(a,b) -> Seq a b) $ seqPair lsPropExpr $ seqPairR (word " |- ") lsPropExpr

lsPropExpr = orP (apply (\(a,b) -> a:b) $ seqPair propExpr (nmanyJ $ seqPairR (word ",") propExpr)) $
                  apply (\a -> []) $ word ""

{-
--this does not work as a path is chosen prematurely and backtracking does not occur (since using Maybe in parser instead of [])
propExpr = orP andExpr $
           orP orExpr $
           orP implyExpr $
           orP notExpr
               nameExpr
-}

--this seems to work, need to convince myself though
--It would be better to upgrade parser to use lists instead of maybe, smallestRem is just a workaround
propExpr = smallestRem [andExpr,
                        orExpr,
                        implyExpr,
                        notExpr,
                        nameExpr]

bracketed p = seqPairR (word "(") $ seqPairL p (word ")")

--ugly with all the whitespace, shorter names would help some
binaryOpExpr op symbolExpr elemExpr rassoc = apply ((if rassoc then foldr1 else foldl1) (\a b -> op a b)) $
                                                      beforeBinaryNmany (whitespace $ 
                                                                         seqPair  elemExpr $ whitespace $
                                                                         seqPairR symbolExpr $ whitespace $
                                                                    whitespacer $ elemExpr)
                                                                        (whitespace $
                                                                          seqPairR symbolExpr $ whitespace $
                                                                       whitespacer elemExpr)
                                       where whitespace = seqPairR $ nmanyJ (word " ")
                                             whitespacer = \x -> seqPairL x (nmanyJ (word " "))

andExpr = binaryOpExpr And (word "^") elemExpr True
      where elemExpr = smallestRem [bracketed implyExpr,
                                    bracketed orExpr,
                                    bracketed andExpr,
                                    notExpr, bracketed notExpr,
                                    nameExpr, bracketed nameExpr]


orExpr = binaryOpExpr Or (word "+") elemExpr True
      where elemExpr = smallestRem [bracketed implyExpr,
                                    bracketed orExpr,
                                    andExpr, bracketed andExpr,
                                    notExpr, bracketed notExpr,
                                    nameExpr, bracketed nameExpr]

implyExpr = binaryOpExpr Imply (word "->") elemExpr True
      where elemExpr = smallestRem [bracketed implyExpr,
                                    orExpr, bracketed orExpr,
                                    andExpr, bracketed implyExpr,
                                    notExpr, bracketed notExpr,
                                    nameExpr, bracketed nameExpr]
notExpr = apply Not $ seqPairR (word "-") elemExpr
      where elemExpr = smallestRem [bracketed implyExpr,
                                    bracketed orExpr,
                                    bracketed andExpr,
                                    notExpr, bracketed notExpr,
                                    nameExpr, bracketed nameExpr]

--could be made more efficient
nameExpr = apply Name $ oneOrMore nameChar
     where nameChar = foldr1 orP $ zipWith char ['a'..'z'] ['a'..'z']


{-
--working towards general order of precedence

indexed ls = zipWith (\x y -> (x,y)) [0..] ls
find f [] = error ""
                find f (x:xs) | f x = x
                              | otherwise = find f xs

--probs want specialised data type at this point
infixMaker :: [(String, a -> b -> v ,Bool)] -> [(String, c -> v)] -> [(String,expr)] -> SubParser () v
infixMaker binaryOps unaryOps constants precedent
             = smallestRem idExprs
          where idExprs = zipWith (,) precedent (map f $ indexed precedent)
                f (i,x) | isBinary x = let elemExpr = smallestRem $ (\(a,b) -> map (brackify . getExpr) a ++ map getExpr b) $
                                                                    splitAt (i+1) precedent --brackify things with same or lower precedent
                                           op = (\(_,b,_)-> b) $ find (\(a,_,_) -> a==x) binaryOps
                                           rassoc = (\(_,_,c)-> c) $ find (\(a,_,_) -> a==x) binaryOps
                                       in binaryOpExpr op x elemExpr rassoc
                        | isUnary x = --idk
                        | isConstant x = --idk
                        | otherwise = error ""
-}
