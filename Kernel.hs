import Parse

{-
Based on Kernel paper and specification
Paper name:
Fexprs as the basis of Lisp function application or $vau: the ultimate abstraction
-}

--Is unfinished

{-
TODO:
simple stuff
better examples

Proper enviroment hierachies
mutation
prims for manipulating enviroments
make-encapsulation-type
{keyed dynamic variables}
etc.
-}

--best way to handle #ignore?
--its got to exist at runTime but thats ugly, even in Expr its not nice
--currently things can get bount to Nil in "bind"

--Allows embedding values in Expr, and has value counterparts to Expr in Value as an experiment, related to M-expression lisp paper?
--would be nicer to embed Expr in value
data Expr = Nil | Cons Expr Expr | Symbol String | ValueE Value | Ignore deriving (Show, Eq)
data Value = Operative Expr Expr Expr Env | Applicative Value | Vau | Wrap | Eval | --Vau, Wrap and Eval should be introduced differently (as should all primitive functions)
             NilV | ConsV Value Value | SymbolV String | IgnoreV |
             EnvV Env deriving (Show, Eq)
type Env = [(Expr,Value)]
-- p-tree args
--swap name args to paras

lookupsym s env = lookupsym' s env
          where lookupsym' s@(Symbol _) []  = error $ "symbol: " ++ show s ++  " not found in env: " ++ show env
                lookupsym' s@(Symbol _) ((s2,v):xs) | s==s2 = v
                                                    | otherwise = lookupsym' s xs

extendEnv vs env = vs ++ env

bind :: Expr -> Value -> Env
bind s@(Symbol _) v = [(s,v)]
bind (Cons a b) (ConsV q w) = bind a q ++ bind b w
bind Nil NilV = []
bind Ignore v = []
bind e v = error $ ""
--add case for ValueE?


--can rename and remove some of these

consVToList :: Value -> [Value]
consVToList NilV = []
consVToList (ConsV a b) = a:(consVToList b)

listToConsV :: [Value] -> Value
listToConsV ls = foldr ConsV NilV ls

mapConsV :: (Value -> Value) -> Value -> Value
mapConsV f cs = listToConsV $ map f $ consVToList cs

--rename exprToValue
consToConsV :: Expr -> Value
consToConsV Ignore = IgnoreV
consToConsV (Symbol s) = SymbolV s
consToConsV Nil = NilV
consToConsV (ValueE a) = a
consToConsV (Cons a b) = ConsV (consToConsV a) (consToConsV b)

consVToCons IgnoreV = Ignore
consVToCons (SymbolV s) = Symbol s
consVToCons NilV = Nil
consVToCons (ConsV a b) = Cons (consVToCons a) (consVToCons b)
consVToCons x = ValueE x

envVToEnv :: Value -> Env
envVToEnv (EnvV e) = e


foldrC :: (Expr -> t -> t) -> t -> Expr -> t
foldrC f i Nil = i
foldrC f i (Cons a b) = f a (foldrC f i b)

foldlC :: (t -> Expr -> t) -> t -> Expr -> t
foldlC f i Nil = i
foldlC f i (Cons a b) = foldlC f (f i a) b

--explicit evaluation is clearer in term reduction
eval :: Expr -> Env -> Value
eval (ValueE x) env = x
eval Nil env = NilV
eval Ignore env = IgnoreV
eval s@(Symbol _) env = lookupsym s env

--move these to combine and add them to primEnv
--need not be primitive given parameter-trees
eval (Cons (Symbol "cons") (Cons a (Cons b Nil))) env = ConsV (eval a env) (eval b env) --applicative
eval (Cons (Symbol "car") (Cons a Nil)) env = case eval a env of
                                                ConsV q w -> q
--

eval (Cons a b) env = combine (eval a env) b env

combine :: Value -> Expr -> Env -> Value
----can be introduced elsewhere
combine Vau operands env = case operands of
                             Cons ptree (Cons denvn (Cons body Nil)) -> Operative ptree denvn body env
                             other -> error $ "Malformed operands in vau: " ++ show other
combine Wrap operands env = case operands of
                              (Cons e Nil) -> Applicative $ eval e env--check eval e env is operative
                              other -> error $ "Malformed operands in wrap:" ++ show other
combine Eval operands env = case operands of
                              (Cons expr (Cons denv Nil)) -> eval (consVToCons $ eval expr env) (envVToEnv $ eval denv env)
----
--seperated Expr and Value types makes things messy
combine (Operative ptree denvn body lenv) operands env = eval body $ extendEnv (bind denvn $ EnvV env) $ extendEnv (bind ptree $ consToConsV operands) lenv
combine (Applicative o) operands env = combine o (foldrC (\x y -> Cons (ValueE (eval x env)) y) Nil operands) env
combine op operands env = error ""

--
t = Cons (Symbol "vau") $ Cons (Symbol "x") $ Cons (Symbol "denv") $ Cons body Nil
  where body = Symbol "x"
t2 = Cons t $ Cons (Symbol "y") Nil
--t3 = Cons t ()
--t = (vau x denv x)
--t2= (t y)
-- (t 1 2 3 4)
t3 = Cons (Symbol "vau") $ Cons (Symbol "x") $ Cons (Symbol "denv") $ Cons res Nil
  where res = Cons (Symbol "cons") $ Cons (Symbol "x") $ Cons (Symbol "x") Nil
t4 = Cons t3 $ Cons (Symbol "y") Nil
--t3 = (vau x denv (cons x x))
--t4 = (t3 y)

-- '(x y z)
-- (eval (list x y z) env)
--with operator
t5 = Cons a $ Cons (Symbol "w") Nil
  where a = Cons (Symbol "vau") $ Cons (Symbol "arg") $ Cons (Symbol "denv") $ Cons res Nil
        res = Cons v2 $ Cons (Symbol "arg") Nil
        v2 = Cons (Symbol "vau") $ Cons (Symbol "arg2") $ Cons (Symbol "denv2") $ Cons res2 Nil
        res2 = Cons (Symbol "eval") $ Cons (Cons (Symbol "car") $ Cons (Symbol "arg2") Nil ) $ Cons (Symbol "denv2") Nil
--with applicative
t6 = Cons a $ Cons (Symbol "w") Nil
  where a = Cons (Symbol "vau") $ Cons (Symbol "arg") $ Cons (Symbol "denv") $ Cons res Nil
        res = Cons v2 $ Cons (Symbol "arg") Nil
        v2 = Cons (Symbol "wrap") $ Cons (Cons (Symbol "vau") $ Cons (Symbol "arg2") $ Cons (Symbol "denv2") $ Cons res2 Nil) Nil
        res2 = Symbol "arg2" --car of
--parameter tree test
t7 =  Cons v $ Cons (Symbol "a") $ Cons (Symbol "b") Nil
   where v = Cons (Symbol "vau") $ Cons (Cons (Symbol "x") $ Cons (Symbol "y") Nil) $ Cons (Symbol "denv") $ Cons body Nil
         body = Symbol "x"

unJust (Just x) = x

--list = Cons (Symbol "wrap ") $ Cons (Cons (Symbol "vau") $ Cons (Symbol "x") $ Cons (Symbol "uenv") $ Cons (Symbol "x") Nil) Nil
list = unJust $ parseExpr "(wrap (vau x #ignore x))"
{-vau = Cons (Symbol "vau") $ Cons (Symbol "args") $ Cons (Symbol "denv") $ Cons res Nil
   where res = Nil--(vau ) -- (eval () _) --defining vau using vau-}
{-
lambda:
(vau (args . body) denv
  (wrap
    (vau argsv #ignore
      (eval (list* ('vau ) argsv) ;;i want symbol vau?, the kernel paper says the operator not the symbol
            denv) ;;eval body in env args=argsv
      )
    )
  )
-}

lambda = unJust $ parseExpr "(vau (args body) denv (wrap (eval (cons vau (cons args (cons #ignore (cons body ())))) denv)))"
_let1 = unJust $ parseExpr "(vau ((name value) body) denv (eval (list (list lambda (list name) body) value) denv))"

t8 = eval (Cons (Cons lambda $ Cons (Symbol "x") $ Cons (Symbol "x") $ Nil) $ Cons (Symbol "wrap") Nil) primEnv

t9 = eval (unJust $ parseExpr expr)
          standardEnv
    where expr = "((lambda (x) (list x x)) (list (list) (list)))"
                  -- (wrap (eval (vau (x) #ignore (list x x)) localEnv))
                  -- (eval `(wrap (vau ,args #ignore ,body)))
primEnv = [(Symbol "vau", Vau),
           (Symbol "wrap", Wrap),
           (Symbol "eval", Eval),
           (Symbol "#ignore", IgnoreV)
          ]
--idk how to arrange this nice, maybe just fold/let* them all
standardEnv = extendEnv e2 $
                        e1
           where e1 = extendEnv [(Symbol "list", eval list primEnv)
                                ,(Symbol "lambda", eval lambda primEnv)
                                ]
                                primEnv
                 e2 = [(Symbol "let1", eval _let1 e1)]

{-
evalParse "((lambda (x y) y) wrap vau)"
evalParse "((wrap (vau (x y) #ignore y)) wrap vau)"
-}
evalPrintParse str = fmap prettyPrint $ evalParse str

class Pretty a where
  prettyPrint :: a -> String
--improve, (a . (b . nil))  = "(a b)"
instance Pretty Expr where
  prettyPrint Nil = "Nil"
  prettyPrint (Symbol s) = s
  prettyPrint (Cons a b) = "(Cons " ++ prettyPrint a ++ " " ++ prettyPrint b ++ ")"
  prettyPrint (ValueE v) = "(ValueE " ++ prettyPrint v ++ ")"
instance Pretty Value where
  prettyPrint (Operative ptree envn body lenv) = "(Operative " ++ prettyPrint ptree ++ " " ++ prettyPrint envn ++ " " ++ prettyPrint body ++ ")"
  prettyPrint (Applicative v) = "(Applicative " ++ prettyPrint v ++ ")"
  prettyPrint Vau = "Vau"
  prettyPrint Wrap = "Wrap"
  prettyPrint Eval = "Eval"
  prettyPrint NilV = "NilV"
  prettyPrint (ConsV a b) = "(ConsV " ++ prettyPrint a ++ " " ++ prettyPrint b ++ ")"
  prettyPrint (SymbolV s) = s-- ?
  prettyPrint IgnoreV = "IgnoreV"
  prettyPrint (EnvV e) = "EnvV" ++ show e

evalParse str = fmap (\x -> eval x standardEnv) $ parseExpr str
--add (a . b) syntax?
parseExpr str = parse (whitespaceSurround exprExpr) str

whitespace = nmanyJ (word " ")
whitespace1 = oneOrMore (word " ")
whitespaceSurround x = seqPairR whitespace $ seqPairL x whitespace


exprExpr = (orP lsExpr
                symbolExpr)
--some common patterns here
lsExpr = orP (seqPairR (word "(") $ seqPairL ls (word ")"))
             (apply (\x -> Nil) $ word "()")
       where ls = apply (\x -> foldr Cons Nil x) $ ls2   -- $ seqPair (nmanyJ $ seqPairL exprExpr (word " "))
             ls2 = orP (whitespaceSurround $ apply (\(x,y) -> x:y) $ seqPair exprExpr (nmanyJ $ seqPairR whitespace1 exprExpr))
                       (always []) --Nil
               -- $ apply (\(x,y) -> x:y) $ seqPair exprExpr $ nmanyJ $ seqPairR whitespace1 $ exprExpr


symbolExpr = apply Symbol $ oneOrMore charExpr
      where charExpr = foldr1 orP $ zipWith char charLs charLs
            charLs = ['a'..'z'] ++ ['#']

--should look at philip wadler pretty print paper

{-
"a    s e "
suroundWhitespace (seq (nmany (seq element " ")) element)
suroundWhitespace (seq element (nmany (seq " " element)))
--suroundWhitespace (nmany (orP (seq element " ")
                                element)) --use this one
-}

