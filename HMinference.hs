{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE PatternSynonyms #-}

import Parse
import Debug.Trace (trace)

import Prelude hiding (lookup)
import Data.List ((\\))


--main function is generate, infers the HM type of a lambda term
--examples at the bottom of this file

--import Data.List.Unique (uniq) --not found
uniq [] = []
uniq (x:xs) = x : (uniq xs \\ [x])


--state monad to have access to a stream of unique symbols
data State s v = State (s -> (v,s))
runState (State f) = f

instance Functor (State s) where
  fmap f ma = State $ \s -> let (a,s2) = runState ma s
                            in (f a,s2)
instance Applicative (State s) where
  pure a = State $ \s -> (a,s)
  mf <*> ma = State $ \s -> let (f,s2) = runState mf s
                                (a,s3) = runState ma s2
                            in (f a,s3)
instance Monad (State s) where
  ma >>= f = State $ \s -> let (a,s2) = runState ma s
                           in runSource (f a) s2

--could be enforced to be a infinite list by using data Stream a = Stream a (Stream a)
type Source a b = State [a] b
runSource = runState

sourceDraw :: Source a a
sourceDraw = State $ \(x:xs) -> (x,xs)

sourceDrawn :: Int -> Source a [a]
sourceDrawn 0 = State $ \s -> ([],s)
sourceDrawn n = do nm <- sourceDraw
                   nms <- sourceDrawn $ n-1
                   return $ nm:nms


--The lifting is a bit ugly, but I have not found a perfect alternative
data Var = Var String deriving (Eq,Show)
data Lambda = Abs Var Lambda | App Lambda Lambda | LLift Var | Let Var Lambda Lambda deriving (Show)

--Encodes the restriction of HM, foralls are top level
data Type = Type MonoType  | Forall [TVar] MonoType deriving (Show,Eq)
data MonoType = MLift TVar | Arrow MonoType MonoType deriving (Eq)
-- should add constant types and a distiction between a monotype "a" and a unknown "a"
data TVar = TVar String deriving (Eq)

--should use a different typeclass for this
bracketed s = "(" ++ s ++ ")"
instance Show MonoType where
 show (MLift tv) = show tv
 show (Arrow t1 t2@(MLift (TVar _))) = show t1 ++ " -> " ++ show t2
 show (Arrow t1 t2) = show t1 ++ " -> " ++ bracketed (show t2)
instance Show TVar where
 show (TVar t) = t


data Context a b = Context [(a,b)]
emptyContext = Context []
lookup v1 (Context []) = Nothing
lookup v1 (Context ((v2,val):rst)) | v1==v2 = Just val
                                   | otherwise = lookup v1 $ Context rst
lsToContext ls = Context ls
addBinding x v (Context c) = Context $ (x,v):c
addBindings binds (Context c) = Context $ binds++c

tvarSource = map TVar $ map (\x->[x]) ['a'..'z'] --I have the full lot in a different file

--Main function
generate :: Lambda -> Type
generate l = generateC emptyContext l

generateC :: Context Var Type -> Lambda -> Type
generateC c l = let ((tp,tpEqs),s) = runSource (generateCSU c l) tvarSource
                    tpSub = unify tpEqs
                in generalise c $ Type $ substituteAll tpSub tp

--Has to substitute in order
substituteAll :: [(TVar,MonoType)] -> MonoType -> MonoType
substituteAll sub t = foldl (\t' (tv,v) -> replace1 tv v t') t sub --foldl'

replace :: Context TVar MonoType -> MonoType -> MonoType
replace c t@(MLift tv@(TVar _)) = maybe t id $ lookup tv c
replace c (Arrow t1 t2) = Arrow (replace c t1) (replace c t2)

replace1 :: TVar -> MonoType -> MonoType -> MonoType
replace1 tv v t = replace (lsToContext $ [(tv,v)]) t


class FreeVars a where
  freeVars :: a -> [TVar]
instance FreeVars Type where
 freeVars (Type t) = freeVars t
 freeVars (Forall tvs t) = freeVars t \\ tvs
instance FreeVars MonoType where
 freeVars (MLift tv@(TVar _)) = [tv]
 freeVars (Arrow a b) = uniq $ freeVars a ++ freeVars b
instance (FreeVars b) => FreeVars (Context a b) where
 freeVars (Context c) = uniq $ foldr (++) [] $ map (\(_,b) -> freeVars b) $ c

--carring some extra context around in equations to give better errors
type ErrorInfo = (Lambda, Lambda, [Lambda]) --third is meant to be the surrounding context, could change to be more space efficient

data Equation a c = Equation a a c
type EquationC a = Equation a ErrorInfo

instance (Show a) => Show (Equation a c) where
 show (Equation a1 a2 c) = "Equation " ++ show a1 ++ " " ++ show a2


recursiveEquationError (Equation t1 t2 (l1,l2,c)) = error $ "\nrecursive type:" ++
                                                            "\ncant solve " ++ show t1 ++ " = " ++ show t2 ++
                                                            "\nin application " ++ show (App l1 l2) ++
                                                            showContext (reverse c)
                                                where showContext [] = []
                                                      showContext (x:xs) = "\nin context " ++ show x ++ showContext xs


--unify could be a lot more general (multiple function symbols, this only has "->"), would there be a problem with threading through the extra information?

--change the error for recursive type into a failure

pattern MTVar :: String -> MonoType
pattern MTVar a = MLift (TVar a)

eqmap f (Equation x y c) = Equation (f x) (f y) c
toTVar (MLift a@(TVar _)) = a

--read the resulting substitution of [x1->e1...xn->en] as doing x1->e1 THEN x2->en ...
--
unify :: [EquationC MonoType] -> [(TVar,MonoType)]
unify [] = []
unify ((Equation t1@(MTVar _) t2@(MTVar _) _):rst) | t1v==t2v = unify rst
                                                   | otherwise = ((t1v,t2):) $ unify $ map (eqmap $ replace1 t1v t2) rst
                                               where t1v = toTVar t1
                                                     t2v = toTVar t2
unify (e@(Equation t1@(MTVar _) t2@(Arrow _ _) _):rst) | or $ map (==t1v) $ freeVars t2 = recursiveEquationError e
                                                       | otherwise = ((t1v,t2):) $ unify $ map (eqmap $ replace1 t1v t2) rst
                                                    where t1v = toTVar t1
unify ((Equation t1@(Arrow _ _) t2@(MTVar _) i):rst) = unify $ (Equation t2 t1 i):rst
unify ((Equation (Arrow a1 a2) (Arrow b1 b2) i):rst) = unify $ (Equation a1 b1 i):(Equation a2 b2 i):rst



generalise :: Context Var Type -> Type -> Type
generalise c (Forall vs t) = Forall ((freeVars t ++ vs) \\ freeVars c) t
generalise c (Type t) = Forall (freeVars t \\ freeVars c) t

instantiate (Forall vs t) = do tvs <- (map MLift) <$> (sourceDrawn $ length vs)
                               let binds = lsToContext $ zip vs tvs
                               return $ replace binds t
instantiate (Type t) = return t


--carry around an equations as state?
generateCSU :: Context Var Type -> Lambda -> Source TVar (MonoType,[EquationC MonoType])
generateCSU c (LLift v@(Var _)) = do t <- instantiate $ maybe (error "var not in context") id $ lookup v c --this assumes the term as been syntax checked, ie. freevars topTerm = []
                                     return (t,[])
generateCSU c e@(Abs v@(Var _) l) = do tv <- MLift <$> sourceDraw
                                       (t,eqs) <- generateCSU (addBinding v (Type tv) c) l
                                       return (Arrow tv t, addContext e eqs)
generateCSU c e@(App l1 l2) = do (t1,eq1) <- generateCSU c l1
                                 (t2,eq2) <- generateCSU c l2
                                 tv <- MLift <$> sourceDraw
                                 let info = (l1,l2,[])
                                 let eqf = (Equation t1 (Arrow t2 tv) info):(addContext e $ eq1 ++ eq2)
                                 return (tv, eqf)
generateCSU c e@(Let v l1 l2) = do (t1,eq1) <- generateCSU c l1
                                   let vt = generalise c (Type t1)
                                   (t2,eq2) <- generateCSU (addBinding v vt c) l2
                                   return (t2, addContext e $ eq1 ++ eq2)
                                
addContext l es = map f es
          where f (Equation t1 t2 (l1,l2,c)) = (Equation t1 t2 (l1,l2,l:c))




--Examples
t1 = generate $ readTerm "let f |k.k ((f |x.|y.x) (f |z.z))"
  --Let (Var "f") (Abs (Var "k") $ LLift $ Var "k") $ App (App (LLift $ Var "f") $ Abs (Var "x") $ Abs (Var "y") $ LLift $ Var "x") (App (LLift $ Var "f") $ Abs (Var "z") $ LLift $ Var "z")
t2 = generate $ readTerm "let f |k.k ((f |x.|y.x) |z.z)"
  --Let (Var "f") (Abs (Var "k") $ LLift $ Var "k") $ App (App (LLift $ Var "f") $ Abs (Var "x") $ Abs (Var "y") $ LLift $ Var "x") (Abs (Var "z") $ LLift $ Var "z")
--t3 should error, it is untypeable
t3 = generate $ readTerm "|y.(y y)"
  --(Abs (Var "y") $ App (LLift $ Var "y") (LLift $ Var "y")) 
t4 = generate $ readTerm "(|f.|z.((f z) z) |x.|y.y)"
  --App (Abs (Var "f") $ Abs (Var "z") $ App (App (LLift $ Var "f") (LLift $ Var "z")) (LLift $ Var "z")) (Abs (Var "x") $ Abs (Var "y") $ LLift $ Var "y")

t5 = generate $ readTerm "(|x.x (let f |k.k (f f)))" --demonstrates polymorphism




--Parser
--gives inflexable syntax
--some results may be suprising eg. readTerm "(|x.x y)" => App (Abs (Var "x") (Var "x")) (Var "y")

pbracketed f = seqPairR (word "(") $ seqPairL f $ (word ")")
unLLift (LLift a) = a

readTerm str = maybe (error "failed to parse") id $ parse termExpr str
termExpr = orP absExpr $ orP letExpr $ orP appExpr $ mvarExpr
absExpr = apply (\(a,b) -> Abs (unLLift a) b) $ seqPairR (word "|") $ seqPair mvarExpr $ seqPairR (word ".") termExpr
letExpr =  apply (\(v,(e1,e2)) -> Let (unLLift v) e1 e2) $ pbracketed $ seqPairR (word "let ") $ seqPair mvarExpr $ seqPairR (word " ") $ seqPair termExpr $ seqPairR (word " ") termExpr
appExpr = apply (\(a,b) -> App a b)   $ seqPairR (word "(") $ seqPair termExpr $ seqPairR (word " ") $ seqPairL termExpr (word ")")
mvarExpr = apply (LLift . Var) $ oneOrMore varChar
    where varChar = foldr1 orP $ map (\a -> char a a) $ ['a'..'z'] ++ ['A'..'Z']

