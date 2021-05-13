module Parse where

{-
Simple parser combinator experiments, trying to figure out stuff on my own.
Many things could be improved:
 Changing from Maybe to []
 Better naming
 Using data types instead of funcitons where possible to preserve information
-}

type SubParser a b = (a,String) -> Maybe (b,String)
type Parser a = SubParser () a
--many type annotations restricts type uneccesseraly

char :: a -> Char -> SubParser b a
char a c (_, []) = Nothing
char a c (_, (x:xs)) | x==c = Just (a,xs)
                     | otherwise = Nothing

--using case instead of applicative/functor functions so I can see whats going on more
seqPair :: SubParser a b -> SubParser a c -> SubParser a (b,c)
seqPair f g (a,str)  = case f (a,str) of
                        Just (b,rem) -> fmap (\(q,rem2) -> ((b,q), rem2)) $ g (a,rem)
                        Nothing -> Nothing

seqPairL f g = apply (\(a,b) -> a) $ seqPair f g
seqPairR f g = apply (\(a,b) -> b) $ seqPair f g

seqP :: SubParser a b -> SubParser b c -> SubParser a c
seqP f g (a,str)  = case f (a,str) of
                     Just (b,rem) -> g (b,rem)
                     Nothing -> Nothing

--need to make decisions on these
seqPl f g (a,str) = case seqP f g (a,str) of
                     Just (b,rem) -> case g (b,rem) of
                                       Just (c,rem2) -> Just (b,rem2)
                                       Nothing -> Nothing
                     Nothing -> Nothing
seqPr f g (a,str) = case seqP f g (a,str) of
                     Just (b,rem) -> case g (b,rem) of--could match on just rem
                                       Just (c,rem2) -> Just (c,rem2)
                                       Nothing -> Nothing
                     Nothing -> Nothing

orP :: SubParser a b -> SubParser a b -> SubParser a b
orP f g (a,str) = case f (a,str) of
                   Just (b,rem) -> Just (b,rem)
                   Nothing -> g (a,str)


nmany :: SubParser a b -> (a, String) -> ([b], String) --theres not a maybe as it always succeeds
nmany f (a,str) = case f (a,str) of
                    Just (b,rem) -> let (bs,remF) = nmany f (a,rem)
                                    in (b:bs,remF)
                    Nothing -> ([],str)

nmanyJ :: SubParser a b -> SubParser a [b]
nmanyJ f q = Just $ nmany f q

oneOrMore :: SubParser a b -> SubParser a [b]
oneOrMore f = apply (\(q,qs) -> q:qs) $ seqPair f (nmanyJ f)

beforeNmany :: SubParser a b -> SubParser a b -> SubParser a [b]
beforeNmany f g = apply (\(a,b) -> a:b) $ seqPair f (nmanyJ g)

beforeBinaryNmany :: SubParser a (b,b) -> SubParser a b -> SubParser a [b]
beforeBinaryNmany f g = apply (\((a,b),cs) -> a:b:cs) $ seqPair f (nmanyJ g)

--hack to get around use of Maybe instead of []
smallestRem :: [SubParser a b] -> SubParser a b
smallestRem ps v = foldr f Nothing $ map ($ v) ps
            where f :: Maybe (b,String) -> Maybe (b,String) -> Maybe (b,String)
                  f Nothing y = y
                  f x Nothing = x
                  f x@(Just (_,rem1)) y@(Just (_,rem2)) | length rem1 <= length rem2 = x
                                                        | otherwise = y

apply :: (b -> c) -> SubParser a b -> SubParser a c 
apply f g (a,str) = fmap (\(v,rem) -> (f v, rem)) $ g (a,str)

{-applyStr :: (String -> c) -> SubParser a b -> SubParser a c
applyStr f g (a,str) = fmap (\(v,rem) -> (f rem, rem)) $ g (a,str)

swap :: SubParser a String -> SubParser a String
swap g (a,str) = fmap (\(v,rem) -> (rem,v)) $ g (a,str)-}

never :: SubParser a b
never (a,str) = Nothing

always :: b -> SubParser a b
always v (a,str) = Just (v,str)

word (x:xs) = apply (\(a,b) -> a:b) $ seqPair (char x x) (word xs)
word [] = apply (\a -> []) $ always ()


parseWith :: SubParser a b -> a -> String -> Maybe b
parseWith expr i str = case expr (i,str) of
                        Just (a,"") -> Just a
                        otherwise -> Nothing

parse :: Parser b -> String -> Maybe b
parse expr str = parseWith expr () str
     

----use examples and experiments
--can be uncommented when I set only the above stuff to be exported
{-

varChar = foldr1 orP $ zipWith char ['a'..'z'] ['a'..'z']

--I prefer seqPair over seqP
{-
var = apply Var $ seqP varChar (\(a,rem) -> 
                                   let Just (b,rem2) = nmanyJ varChar ('q',rem)
                                   in Just (a:b,rem2))
-}
var = apply (\(c,cs) -> Var $ c:cs) $ seqPair varChar (nmanyJ varChar)

data Lambda = Var String | Abs Lambda Lambda | App Lambda Lambda deriving Show

--parse var2 "somevarname"

labs = apply (\(v,e) -> Abs v e) $ seqPairR (char '|' '|') $ seqPair var $ seqPairR (char '.' '.') lexpr
app = apply (\(a,b) -> App a b) $ seqPairR (char '(' '(') $ seqPair lexpr $ seqPairR (char ' ' ' ') $ seqPairL lexpr (char ')' ')')
lexpr = orP var $ orP labs app
--parse lexpr "|x.x"


numChar = orP (char 0 '0') (char 1 '1')
number = apply (\(a,bs) -> foldr (+) 0 (a:bs)) $ seqPair numChar (nmanyJ numChar)


data Lisp = Symbol String | Cons Lisp Lisp | Nil deriving Show

symbolChar = foldr1 orP $ zipWith char ['a'..'z'] ['a'..'z']--generalise
--symbol = Seq (\a b -> Symbol $ a:b) symbolChar $ NMany id symbolChar
symbol = apply Symbol $ oneOrMore symbolChar
constant = never

atom = orP symbol constant

nil = apply (\_ -> Nil) $ seqPair (char '(' '(') (char ')' ')')--nil not in atom?
--list = Or nil $ seqR (char '(') $ Seq (\a b -> foldr Cons Nil $ a:b) expr $ seqL (NMany id $ seqR (char ' ') expr) (char ')')
list = orP nil $ 
       seqPairR (char '(' '(') $ 
         apply (\(a,b) -> foldr Cons Nil $ a:b) $ seqPair expr $ seqPairL (nmanyJ $ seqPairR (char ' ' ' ') expr) 
       (char ')' ')')--how could I make this neater??

expr = orP atom list

{-
--infix syntax?
list = nil <|>
       '(' *>
         (apply (\(a,b) -> foldr Cons Nil $ a:b) 
            expr <*> (nmanyJ $ ' ' *> expr) )
       <* ')'
-}
--nil <|> 
--  (apply (\(a,b) -> foldr Cons Nil $ a:b) $ 
--     '(' *> (expr <*> nmany (' ' *> expr)) <* ')')

test1 = parse lexpr "(|x.|z.(x z) |y.y)"
test2 = parse expr "(a (b c) d ((e f) (g h)))" 

test3 = parse lexpr "(|x.|z.(x z) |y.y" --should fail
test4 = parse expr "(q q) w" --should fail


-}
