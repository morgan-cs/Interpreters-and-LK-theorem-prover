import Prelude hiding (lookup)
import Data.List ((\\))

{-
Pretty rough with some experiments, trying to get both breadth and depth traversal of the whatever tree
--I remember a paper that presents prolog as manipulating finite but self referential trees
Mostly works (I think only missing negation for the pure subset of prolog)
Use examples at the bottom

Needs a parser
-}

uniq [] = []
uniq (x:xs) = x:((uniq xs) \\ [x])

data Tree a = Leaf a | Node [Tree a] | GetString (String -> Tree a)

runTree :: Tree a -> [a]
runTree t = runTree_ "" t

runTree_ :: String -> Tree a -> [a]
runTree_ s (Leaf a) = [a]
runTree_ s (Node ts) = concat $ zipWith f (split s) ts
                   where f = runTree_
                         {- --do something to only split when needed
                         f s2 (Leaf a) =
                         f s2 ()
                         -}
runTree_ s (GetString st) = runTree_ s (st s) --only split here???

data RoseTree a = RLeaf a | RNode [RoseTree a]
runTree__ :: String -> Tree a -> RoseTree a
runTree__ s (Leaf a) = RLeaf a
runTree__ s (Node ts) = RNode $ zipWith f (split s) ts
                     where f = runTree__
runTree__ s (GetString st) = runTree__ s (st s) --split??

depth :: RoseTree a -> [a]
depth (RLeaf a) = [a]
depth (RNode ts) = concat $ map depth ts

breadth :: RoseTree a -> [a]
breadth t = breadth' [t]
breadth' ::  [RoseTree a] -> [a]
breadth' [] = []
breadth' ((RLeaf a):xs) = a:(breadth' xs)
breadth' ((RNode ts):xs) = breadth' $ xs++ts

split s = map (\x -> x++"_"++s) allCodes

allCodes = nexts [""]
    where alphabet = ['a'..'z']
          nexts ns = let next = [ c:n | n <- ns, c <- alphabet]
                     in next ++ nexts next



instance Functor RoseTree where
  fmap f (RLeaf a) = RLeaf $ f a
  fmap f (RNode ts) = RNode $ map (fmap f) ts

instance Applicative RoseTree where
  pure = RLeaf
  (RLeaf f) <*> ma = fmap f ma
  (RNode fs) <*> ma = RNode $ map (<*> ma) fs

instance Monad RoseTree where
  return = pure
  (RLeaf a) >>= amb = amb a
  (RNode ts) >>= amb = RNode $ map (>>= amb) ts
  {-
  join (Leaf ma) = ma
  join (RNode tts) = RNode $ map join tts

  amb >=> bmc = \a -> amb a >>= bmc
  -}
  
  
instance Functor Tree where
  fmap f (Leaf a) = Leaf $ f a
  fmap f (Node ts) = Node $ map (fmap f) ts
  fmap f (GetString st) = GetString $ \s -> fmap f (st s)

instance Applicative Tree where
  pure = Leaf
  (Leaf f) <*> ma = fmap f ma
  (Node tfs) <*> ma = Node $ map (<*> ma) tfs
  (GetString sf) <*> ma = GetString $ \s -> (sf s) <*> ma

instance Monad Tree where
  return = pure
  (Leaf a) >>= amb = amb a
  (Node tas) >>= amb = Node $ map (>>= amb) tas
  (GetString sta) >>= amb = GetString $ \s -> (sta s) >>= amb
  {-
  join (Leaf ma) = ma
  join (Node tts) = Node $ map join tts
  join (GetString msta) = GetString $ \s -> join (msta s)

  amb >=> bmc = \a -> amb a >>= bmc
  -}


treeFromList ls = Node $ map Leaf ls
choose = treeFromList
getString = GetString $ \s-> Leaf s
--getCode or something instead?
genSyms = do s <- getString
             return $ map (\a -> s ++ show a) [0..]
  
tst = runTree tst_
tst_ = do x <- treeFromList [1,2,3]
          s <- getString
          y <- treeFromList [1,2,3]
          s2 <- getString
          return $ (x,s,y,s2)
          
tst2 = runTree tst2_
tst2_ = do x <- treeFromList [1,2,3]
           s <- getString
           return $ (x,s)

tst3d = depth $ runTree__ "" tst3_
tst3b = breadth $ runTree__ "" tst3_
tst3_ = do x <- treeFromList [1,2,3]
           if x==2 then do y <- treeFromList [1,2,3]
                           return (x,y)
           else return (x,x)


--prolog stuff
--ADD a Not
data Term = Var String | Constant String | Cons Term Term | Nil deriving (Eq,Show)
data Prop = Predicate String [Term] | PTrue | PFalse | And Prop Prop | Or Prop Prop deriving Show
data Rule = Imply Prop Prop | Fact Prop deriving Show
--could change Fact to Imply PTrue Prop

type Bindings = [(Term,Term)]
--assumes no recursive bindings and has binding shadowing
lookup :: Bindings -> Term -> Maybe Term
lookup b (Cons x y) = Just Cons <*> lookup b x <*> lookup b y --lookup b x >>= (\x1 -> lookup b y >>= (\y1 -> Just $ Cons x1 y1))
lookup b t = f b --could use a map or fold etc.
       where f [] = Nothing
             f ((x,v):xs) | x==t = maybe (Just v) Just $ lookup b v
                          | otherwise = f xs

--tons of this is really boilerplaty
class SubAble a where
  sub :: Bindings -> a -> a
instance SubAble Term where
  sub bs v@(Constant _) = v
  sub bs v@(Var _) = maybe v id $ lookup bs v
  sub bs (Cons a b) = Cons (sub bs a) (sub bs b)
  sub bs Nil = Nil
instance SubAble Prop where
  sub bs (Predicate n ts) = Predicate n (map (sub bs) ts)
  sub bs (And a b) = And (sub bs a) (sub bs b)
  sub bs (Or a b) = Or (sub bs a) (sub bs b)
  sub bs PTrue = PTrue
  sub bs PFalse = PFalse
instance SubAble Rule where
  sub bs (Fact v) = Fact $ sub bs v
  sub bs (Imply a b) = Imply (sub bs a) (sub bs b)

class HasVars a where
  allVars :: a -> [Term]
instance HasVars Term where
  allVars (Constant _) = []
  allVars v@(Var _) = [v]
  allVars (Cons a b) = uniq $ allVars a ++ allVars b
  allVars Nil = []
instance HasVars Prop where
  allVars (Predicate n ts) = uniq $ concatMap allVars ts
  allVars (And a b) = uniq $ allVars a ++ allVars b
  allVars (Or a b) = uniq $ allVars a ++ allVars b
  allVars PTrue = []
  allVars PFalse = []
instance HasVars Rule where
  allVars (Fact a) = allVars a
  allVars (Imply a b) = uniq $ allVars a ++ allVars b


rename :: Rule -> Tree Rule
rename r = do vs <- fmap (map Var) genSyms
              return $ sub (zip (allVars r) vs) r

--without filter it shows failures as []
qD t = filter (/=[]) $ depth t
qB t = filter (/=[]) $ depth t

--queryTop :: Prop -> [Rule] -> [Bindings]
--could have a runTree__ that takes Tree (Maybe a) -> RoseTree a?
--have depth not return Nothings
queryTop p rs = onlyGivenVars $ withoutEmpty $ breadth $ runTree__ "" $ query p rs []
        where vars = allVars p
              unJust (Just a) = a
              --unfortunate cant do these on the roseTree
              withoutEmpty t = map unJust $ filter (/=Nothing) t
              onlyGivenVars t = map (\bd->map (\v->(v,unJust $ lookup bd v)) vars) t

-------------------------need a different representation of failure that []-----------------
--returned [Bindings] in prev, so a list of no bindings was a failure
{-
query :: Prop -> [Rule] -> Bindings -> Tree Bindings
query p@(Predicate _ _) rs bnds = do r <- choose rs >>= rename
                                     case r of
                                       Fact f -> maybe (return []) (\x -> return x) $ unify p f bnds
                                       Imply bdy hd -> maybe (return []) (\x->query bdy rs x) $ unify p hd bnds
query (And p1 p2) rs bnds = do bnds2 <- query p1 rs bnds
                               query p2 rs bnds2
query (Or p1 p2) rs bnds = do r1 <- query p1 rs bnds
                              r2 <- query p2 rs bnds
                              choose [r1,r2]
query PTrue rs bnds = return bnds
query PFalse rs bnds = return []
-}
--the nothing is to aggressive,t3=nothing on all bindings
query :: Prop -> [Rule] -> Bindings -> Tree (Maybe Bindings)
query p@(Predicate _ _) rs bnds = do r <- choose rs >>= rename
                                     case r of
                                       Fact f -> return $ unify p f bnds
                                       Imply bdy hd -> maybe (return Nothing) (\x->query bdy rs x) $ unify p hd bnds
query (And p1 p2) rs bnds = do bnds2 <- query p1 rs bnds
                               maybe (return Nothing) (\x->query p2 rs x) bnds2
query (Or p1 p2) rs bnds = do r1 <- query p1 rs bnds
                              r2 <- query p2 rs bnds
                              choose [r1,r2]
query PTrue rs bnds = return $ Just bnds
query PFalse rs bnds = return $ Nothing

-- copied, may need improving
unify :: Prop -> Prop -> Bindings -> Maybe Bindings
unify (Predicate n1 as1) (Predicate n2 as2) binds | n1==n2 = unifyTerms as1 as2 binds
--not practically used
unify PTrue _ binds = Just binds
unify _ PTrue binds = Just binds
unify PFalse _ binds =  Nothing
unify _ PFalse binds =  Nothing
unify _ _ _ = Nothing


lsToCons = foldr Cons Nil
--zipWith (\(x,y) -> unifyTerm x y binds) as bs
unifyTerms :: [Term] -> [Term] -> Bindings -> Maybe Bindings
unifyTerms as bs binds | length as == length bs = unifyTerm (lsToCons as) (lsToCons bs) binds
                       | otherwise = Nothing


--does not do an occurs checkc for recusive binding, so not proper unification
isBound bs t = maybe False (\x->True) $ lookup bs t
unifyTerm :: Term -> Term -> Bindings -> Maybe Bindings
--fullbind ???
--do sub before?
unifyTerm (Constant a) (Constant b) binds  | a==b = Just binds
unifyTerm a@(Var _) b binds | isBound binds a = unifyTerm (sub binds a) b binds --make better
unifyTerm a b@(Var _) binds | isBound binds b = unifyTerm a (sub binds b) binds
unifyTerm a@(Var _) b binds = Just $ (a,b):binds
unifyTerm a b@(Var _) binds = Just $ (b,a):binds
unifyTerm (Cons a1 a2) (Cons b1 b2) binds = unifyTerm a1 b1 binds >>= (\x -> unifyTerm a2 b2 x) --
unifyTerm Nil Nil binds = Just binds
unifyTerm a b binds = Nothing







t1 = queryTop (Predicate "f" [Var "X"]) [Fact $ Predicate "g" [Constant "v"],
                                         Imply (Predicate "g" [Var "Y"])
                                               (Predicate "f" [Var "Y"])]
t2 = queryTop (Predicate "sib" [Var "X",Var "Y"]) [Fact $ Predicate "parchild" [Constant "p1", Constant "c1"],
                                                   Fact $ Predicate "parchild" [Constant "p1", Constant "c2"],
                                                   Imply (And (Predicate "parchild" [Var "Q", Var "Z"]) (Predicate "parchild" [Var "Q",Var "K"]))
                                                         (Predicate "sib" [Var "Z", Var "K"])]
t3 = queryTop (Predicate "sib" [Var "X",Var "Y"]) [Fact $ Predicate "motherchild" [Constant "trude", Constant "sally"],
                                                Fact $ Predicate "fatherchild" [Constant "tom", Constant "sally"],
                                                Fact $ Predicate "fatherchild" [Constant "tom", Constant "erica"],
                                                Fact $ Predicate "fatherchild" [Constant "mike", Constant "tom"],
                                Imply (And (Predicate "parchild" [Var "Q", Var "Z"]) (Predicate "parchild" [Var "Q",Var "K"]))
                                      (Predicate "sib" [Var "Z", Var "K"]),
                                Imply (Predicate "fatherchild" [Var "X",Var "Y"]) (Predicate "parchild" [Var "X",Var "Y"]),
                                Imply (Predicate "motherchild" [Var "X",Var "Y"]) (Predicate "parchild" [Var "X",Var "Y"])]
t4 = queryTop (Predicate "sib" [Var "X",Var "Y"]) [Fact $ Predicate "parchild" [Constant "trude", Constant "sally"],
                                                Fact $ Predicate "parchild" [Constant "tom", Constant "sally"],
                                                Fact $ Predicate "parchild" [Constant "tom", Constant "erica"],
                                                Fact $ Predicate "parchild" [Constant "mike", Constant "tom"],
                                Imply (And (Predicate "parchild" [Var "Q", Var "Z"]) (Predicate "parchild" [Var "Q",Var "K"]))
                                      (Predicate "sib" [Var "Z", Var "K"])]

appendProg = [Fact $ Predicate "append" [Nil, Var "Xs", Var "Xs"],
              Imply (Predicate "append" [Var "Xs",Var "Ys",Var "Zs"])
                    (Predicate "append" [Cons (Var "X") (Var "Xs"),Var "Ys",Cons (Var "X") (Var "Zs")])]
t5 = queryTop (Predicate "append" [Var "x",lsToCons $ map Constant ["c","d"],
                                   lsToCons $ map Constant ["a","b","c","d"]])
           appendProg

t51 = unify (Predicate "append" [Var "x",lsToCons $ map Constant ["c","d"],lsToCons $ map Constant ["a","b","c","d"]]) (Predicate "append" [Cons (Var "X") (Var "Xs"),Var "Ys",Cons (Var "X") (Var "Zs")]) []
t52 = queryTop (Predicate "append" [Var "X",lsQ ["b"],lsQ ["a","b"]]) appendProg
lsQ ls = lsToCons $ map Constant ls

