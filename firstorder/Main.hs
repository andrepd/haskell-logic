{-# LANGUAGE ParallelListComp #-}

import Parser
import AST

import Data.List (intercalate, nub, sort)
import Data.Function ((&))
import Data.Maybe (fromJust)
import Data.List (find, delete)
import Data.Char (isAlphaNum, isDigit)

import Debug.Trace(trace, traceShow, traceShowId)
-- trace _     = id
-- traceShow _ = id
-- traceShowId = id

type Valuation a = String -> a  -- Variables
type Interpretation a = ( [a]                      -- Domain
                        , String -> ([a] -> a)     -- Functions
                        , String -> ([a] -> Bool)  -- Predicates
                        )

prettyPrint :: Formula -> String
prettyPrint f = case f of 
    Val x -> case x of
        True -> "⊤"
        False -> "⊥"
    -- Pred name args -> name ++ "(" ++ intercalate "," (map prettyPrintTerm args) ++ ")"    
    Pred name args | all isIdent name -> name ++ "(" ++ intercalate "," (map prettyPrintTerm args) ++ ")"  -- R(x1,...,xN) notation
                    | otherwise        -> "(" ++ intercalate name (map prettyPrintTerm args) ++ ")"  -- Infix notation
    Not x -> "¬" ++ prettyPrint x
    And x y -> "(" ++ prettyPrint x ++ " ∧ " ++ prettyPrint y ++ ")"
    Or x y -> "(" ++ prettyPrint x ++ " ∨ " ++ prettyPrint y ++ ")"
    Imp x y -> "(" ++ prettyPrint x ++ " ⇒ " ++ prettyPrint y ++ ")"
    Iff x y -> "(" ++ prettyPrint x ++ " ⇔ " ++ prettyPrint y ++ ")"
    -- Forall x (Forall y p) -> "(∀" ++ x ++ ". " ++ prettyPrint p ++ ")"
    -- Exists x (Forall y p) -> "(∃" ++ x ++ ". " ++ prettyPrint p ++ ")"
    Forall x p -> "(∀" ++ x ++ ". " ++ prettyPrint p ++ ")"
    Exists x p -> "(∃" ++ x ++ ". " ++ prettyPrint p ++ ")"
  where
    prettyPrintTerm :: Term -> String
    prettyPrintTerm x = case x of
        Var x -> x
        -- Func name args -> name ++ "(" ++ intercalate "," (map prettyPrintTerm args) ++ ")"
        Func name args | all isDigit name -> name  -- Digit
                        | all isIdent name -> name ++ "(" ++ intercalate "," (map prettyPrintTerm args) ++ ")"  -- f(x,y) notation
                        | otherwise        -> "(" ++ intercalate name (map prettyPrintTerm args) ++ ")"  -- Infix (x⋆y) notation
    isIdent c = (isAlphaNum c) || (c=='\'') || (c=='_')
    -- collapse :: (a -> b -> c) -> a -> b -> [a]
    -- collapse func x y = case y of
    --     func z w -> x : collapse func z w
    --     _ -> [x]
    -- -- And x (And y (Val True))

-- Helper functions
-- Returns a total function (String -> Term) that maps a to b and is the identity for all other inputs
-- (|=>) :: String -> Term -> (String -> Term)
-- (|=>) a b x | x == a    = b
--             | otherwise = Var x

-- "Amends" a (String -> Term) function such that it now also maps a to b
-- (|->) :: String -> Term -> (String -> Term) -> (String -> Term)
-- (|->) a b f x | x == a    = b
              -- | otherwise = f x

-- "Amends" a function such that it now maps a to b (and keeps all other inputs x mapped to f x)
(|->) :: (Eq a) => a -> b -> (a -> b) -> (a -> b)
(|->) a b f x | x == a    = b
              | otherwise = f x

-- Returns a total function (String -> Term) that maps a to b and is the identity for all other inputs
(|=>) :: String -> Term -> (String -> Term)
(|=>) a b = (|->) a b Var

-- Value of a term in a given interpretation and valuation
termval :: Interpretation a -> Valuation a -> Term -> a
termval m@(domain, funcInterp, predInterp) v f = case f of
    Var x -> v x
    Func name args -> func $ map (termval m v) args where func = funcInterp name

-- Checks if a formula holds in a given valuation and interpretation
holds :: Interpretation a -> Valuation a -> Formula -> Bool
holds m@(domain, funcInterp, predInterp) v f = case f of
    Val x -> x
    Pred name args -> pred $ map (termval m v) args where pred = predInterp name
    Not x -> not (holds m v x)
    And x y -> (holds m v x) && (holds m v y)
    Or  x y -> (holds m v x) || (holds m v y)
    Imp x y -> not (holds m v x) || (holds m v y)
    Iff x y -> (holds m v x) == (holds m v y)
    Forall x p -> all (\a -> holds m ((x |-> a) v) p) domain
    Exists x p -> any (\a -> holds m ((x |-> a) v) p) domain

-- Substitute variable a for b in f
subst :: (String -> Term) -> Formula -> Formula
-- subst s f | trace ("subst " ++ show f) False = undefined
subst s f = case f of
    Val _ -> f
    Pred name args -> Pred name $ map (substInTerm s) args
    Not x -> Not $ subst s x
    And x y -> subst s x `And` subst s y
    Or  x y -> subst s x `Or`  subst s y
    Imp x y -> subst s x `Imp` subst s y
    Iff x y -> subst s x `Iff` subst s y
    Forall x p -> if s x /= Var x
        then error "Cannot substitute bound variable"
        else if needsRename x p then Forall x' (subst ((x |-> Var x') s) p) else Forall x (subst s p) where x' = variant x $ x : freeVars f
    Exists x p -> if s x /= Var x
        then error "Cannot substitute bound variable"
        else if needsRename x p then Exists x' (subst ((x |-> Var x') s) p) else Exists x (subst s p) where x' = variant x $ x : freeVars f
  where
    substInTerm :: (String -> Term) -> Term -> Term
    substInTerm s f = case f of
        Var x -> s x
        Func name args -> Func name (map (substInTerm s) args)
    -- Checks if a bound variable needs renaming (if a substitution would cause a variable to be captured by a quantifier, then we need to "alpha-convert" to avoid the clash)
    needsRename x p = any (\y -> x `elem` (varsTerm $ s y)) (freeVars $ Forall x p)

-- List of variables in formula
vars :: Formula -> [String]
vars = nub . vars' where
    vars' :: Formula -> [String]
    vars' f = case f of
        Val x -> []
        Pred _ args -> concat $ map varsTerm args 
        Not x -> vars' x
        And x y -> vars' x ++ vars' y
        Or  x y -> vars' x ++ vars' y
        Imp x y -> vars' x ++ vars' y
        Iff x y -> vars' x ++ vars' y
        Forall x p -> x : vars' p
        Exists x p -> x : vars' p

-- List of variables in term
varsTerm :: Term -> [String]
varsTerm = nub . varsTerm' where
    varsTerm' f = case f of
        Var x -> [x]
        Func _ args -> concat $ map varsTerm' args 

-- List of free variables in formula
freeVars :: Formula -> [String]
freeVars = nub . freeVars' where
    freeVars' :: Formula -> [String]
    freeVars' f = case f of
        Val x -> []
        Pred _ args -> concat $ map varsTerm args 
        Not x -> freeVars' x
        And x y -> freeVars' x ++ freeVars' y
        Or  x y -> freeVars' x ++ freeVars' y
        Imp x y -> freeVars' x ++ freeVars' y
        Iff x y -> freeVars' x ++ freeVars' y
        Forall x p -> x `delete` freeVars p
        Exists x p -> x `delete` freeVars p

-- Formula is closed (or a sentence) if it has no free variables, open if it has some free variables, and ground if it has no variables at all
isClosed = null . freeVars
isOpen = not . isClosed
isGround = null . vars

-- Universal closure
universalClosure :: Formula -> Formula
universalClosure f = let
    v = freeVars f
    in foldr Forall f v

-- Fresh variable
{-
freshVar :: Formula -> String
freshVar f = 
    let identifiers = [ c:s | s <- "":identifiers, c <- ['a'..'z'] ]
    -- in  fromJust $ find (`notElem` vars f) identifiers
        v = vars f
        maxvar = maximum v
    in  dropWhile (/= maxvar) identifiers !! 1
-}

variant :: String -> [String] -> String
-- variant x xs | trace ("variant " ++ show x) False = undefined
variant x xs = if x `elem` xs then variant (x++"'") xs else x

-- Simplify: remove tautologies
simplify :: Formula -> Formula
simplify f = 
    let simplify' f = case f of
            Not (Val True) -> Val False
            Not (Val False) -> Val True
            Not (Not x) -> x
            And (Val True) x -> x
            And x (Val True) -> x
            And (Val False) x -> Val False
            And x (Val False) -> Val False
            Or (Val True) x -> Val True
            Or x (Val True) -> Val True
            Or (Val False) x -> x
            Or x (Val False) -> x
            Imp (Val True) x -> x
            Imp x (Val True) -> Val True
            Imp (Val False) x -> Val True  -- a => b === a <= b
            Imp x (Val False) -> Not x
            Iff (Val True) x -> Val True
            Iff x (Val True) -> Val True
            Iff (Val False) x -> Val False
            Iff x (Val False) -> Val False
            Forall x p -> if x `elem` freeVars p then f else p
            Exists x p -> if x `elem` freeVars p then f else p
            _ -> f
    in  case f of
            Not x -> simplify' $ Not $ simplify x
            And x y -> simplify' $ And (simplify x) (simplify y)
            Or  x y -> simplify' $ Or  (simplify x) (simplify y)
            Imp x y -> simplify' $ Imp (simplify x) (simplify y)
            Iff x y -> simplify' $ Iff (simplify x) (simplify y)
            Forall x p -> simplify' $ Forall x (simplify p)
            Exists x p -> simplify' $ Exists x (simplify p)
            _ -> f

-- Negation normal form: push negations down
nnf :: Formula -> Formula
nnf = nnf' . simplify where
    nnf' f = case f of
        And x y -> And (nnf' x) (nnf' y)
        Or  x y -> Or (nnf' x) (nnf' y)
        Imp x y -> Or (nnf' $ Not x) (nnf' y)
        Iff x y -> Or (And (nnf' x) (nnf' y)) (And (nnf' $ Not x) (nnf' $ Not y))
        Not (Not x) -> nnf' x
        Not (And x y) -> Or  (nnf' $ Not x) (nnf' $ Not y)
        Not (Or  x y) -> And (nnf' $ Not x) (nnf' $ Not y)
        Not (Imp x y) -> And (nnf' x) (nnf' $ Not y)
        Not (Iff x y) -> Or (And (nnf' x) (nnf' $ Not y)) (And (nnf' $ Not x) (nnf' y))
        Forall x p -> Forall x (nnf' p)
        Exists x p -> Exists x (nnf' p)
        Not (Forall x p) -> Exists x (nnf' $ Not p)
        Not (Exists x p) -> Forall x (nnf' $ Not p)
        _ -> f

-- Prenex normal form: pull quantifiers out
pnf :: Formula -> Formula
pnf = pnf' . nnf where
    -- pnf' f | trace ("pnf " ++ show f) False = undefined
    pnf' f = case f of
        And x y -> aux $ And (pnf' x) (pnf' y)
        Or  x y -> aux $ Or  (pnf' x) (pnf' y)
        Forall x p -> Forall x (pnf' p)
        Exists x p -> Exists x (pnf' p)
        _ -> f
    -- aux f | trace ("aux " ++ show f) False = undefined
    aux f = case f of
        And (Forall x p) (Forall y q) -> Forall z (aux $ subst (x |=> Var z) p `And` subst (y |=> Var z) q) where z = variant x $ freeVars f
        Or  (Exists x p) (Exists y q) -> Exists z (aux $ subst (x |=> Var z) p `Or`  subst (y |=> Var z) q) where z = variant x $ freeVars f
        And (Forall x p) q -> Forall x' (aux $ subst (x |=> Var x') p `And` q) where x' = variant x $ freeVars f
        And q (Forall x p) -> Forall x' (aux $ q `And` subst (x |=> Var x') p) where x' = variant x $ freeVars f
        Or  (Forall x p) q -> Forall x' (aux $ subst (x |=> Var x') p `Or`  q) where x' = variant x $ freeVars f
        Or  q (Forall x p) -> Forall x' (aux $ q `Or`  subst (x |=> Var x') p) where x' = variant x $ freeVars f
        And (Exists x p) q -> Exists x' (aux $ subst (x |=> Var x') p `And` q) where x' = variant x $ freeVars f
        And q (Exists x p) -> Exists x' (aux $ q `And` subst (x |=> Var x') p) where x' = variant x $ freeVars f
        Or  (Exists x p) q -> Exists x' (aux $ subst (x |=> Var x') p `Or`  q) where x' = variant x $ freeVars f
        Or  q (Exists x p) -> Exists x' (aux $ q `Or`  subst (x |=> Var x') p) where x' = variant x $ freeVars f
        _ -> f



--- Skolemnization ---

-- List all functions and respective arities in a given formula
funcs :: Formula -> [(String, Int)]
funcs = nub . funcs' where
    funcs' f = case f of
        Val x -> []
        Pred _ args -> concat $ map funcsTerm args
        Not x -> funcs' x
        And x y -> funcs' x ++ funcs' y
        Or  x y -> funcs' x ++ funcs' y
        Imp x y -> funcs' x ++ funcs' y
        Iff x y -> funcs' x ++ funcs' y
        Forall x p -> funcs' p
        Exists x p -> funcs' p
      where
        funcsTerm f = case f of
            Var _ -> []
            Func name args -> (name, length args) : (concat $ map funcsTerm args)


-- Opposite of universal closure: remove leading universal quantifiers
specialize :: Formula -> Formula
specialize f = case f of
    Forall _ p -> specialize p
    _ -> f

-- Skolemization:
-- Put in NNF |> skolemize proper |> put in PNF |> remove universal quantifiers
skolem :: Formula -> Formula
skolem f = specialize $ pnf $ snd $ skolem' (map fst $ funcs f) $ nnf f where
    skolem' :: [String] -> Formula -> ([String], Formula)
    skolem' names f = case f of
        Exists x p -> 
            let v = freeVars f
                name = variant (if null v then "c_"++x else "f_"++x) names
                func = Func name (map Var v)
            in  skolem' (name:names) (subst (x |=> func) p)
        Forall x p -> let (names', p') = skolem' names p in (names', Forall x p')
        And x y -> skolemBin names And x y
        Or  x y -> skolemBin names Or  x y
        _ -> (names, f)
    skolemBin names fn x y = 
        let (names',  x') = skolem' names  x
            (names'', y') = skolem' names' y
        in  (names'', fn x' y')


----

extract (Right x) = x
extract (Left y) = error $ show y

putLn = putStrLn ""

boolToSign True  = "✓"
boolToSign False = "✗"

boolInterp :: Interpretation Bool
boolInterp =
    let dom = [True,False]
        func "0" [] = False
        func "1" [] = True
        func "+"  [x,y] = not $ x == y
        func "*" [x,y] = x && y
        func _ _ = error "Bad function"
        pred "eq" [x,y] = x == y
        pred _ _ = error "Bad predicate"
    in (dom, func, pred)

modNInterp :: Int -> Interpretation Int
modNInterp n =
    let dom = [0..n-1]
        func "0" [] = 0 `mod` n
        func "1" [] = 1 `mod` n
        func "+"  [x,y] = (x+y) `mod` n
        func "*" [x,y] = (x*y) `mod` n
        func _ _ = error "Bad function"
        pred "eq" [x,y] = x == y
        pred _ _ = error "Bad predicate"
    in (dom, func, pred)



main = do
{-    inp <- getLine
    putLn
    let formula = (extract . parseExp) inp
    putStrLn $ show $ formula
    putStrLn $ prettyPrint $ formula-}

    {-let formula1 = (extract . parseExp) "@x . eq(x,0) | eq(x,1)"
    -- putStrLn $ show formula1
    putStrLn $ prettyPrint formula1
    putStrLn $ show $ holds boolInterp undefined formula1
    putStrLn $ show $ holds (modNInterp 2) undefined formula1
    putStrLn $ show $ holds (modNInterp 3) undefined formula1
    putStrLn $ show $ vars formula1
    putStrLn $ show $ freeVars formula1
    -- putStrLn $ show $ freshVar formula1
    putLn

    -- let formula2 = (extract . parseExp) "@x. ~eq(x,0) => \\y. eq(times(x,y),1)"
    -- let formula2 = (extract . parseExp) "@x. ~(x=0) => \\y. x*y = 1"
    let formula2 = (extract . parseExp) "@x. ~eq(x,0) => \\y. eq(x*y , 1)"
    -- putStrLn $ show formula2
    putStrLn $ prettyPrint formula2
    putStrLn $ show $ filter (\n -> holds (modNInterp n) undefined formula2) [1..100]
    putStrLn $ show $ vars formula2
    putStrLn $ show $ freeVars formula2
    -- putStrLn $ show $ freshVar formula2-}

    -- let formula = getLine >>= (extract . parseExp)
    inp <- getLine
    let formula = (extract . parseExp) inp
    putStr "AST:            "
    putStrLn $ show formula
    putStr "Prettyprint:    "
    putStrLn $ prettyPrint formula
    -- putStrLn $ prettyPrint $ subst "x" (Var "y") formula
    putStr "Variables:      "
    putStrLn $ show $ vars formula
    putStr "Free variables: "
    putStrLn $ show $ freeVars formula
    -- putStrLn $ show $ freshVar formula
    putStr "Univ. Closure:  "
    putStrLn $ prettyPrint $ universalClosure formula
    -- putStrLn $ prettyPrint $ subst (\x -> if x=="x" then Var "y" else Var x) formula
    -- putStr "Subst x->y:  "
    -- putStrLn $ prettyPrint $ subst ("x" |=> Var "y") formula
    putStr "Simplified:     "
    putStrLn $ prettyPrint $ simplify formula
    -- putStrLn $ show $ simplify formula
    putStr "NNF:            "
    putStrLn $ prettyPrint $ nnf formula
    putStr "PNF:            "
    putStrLn $ prettyPrint $ pnf formula
    putStr "Funcs:          "
    putStrLn $ show $ funcs formula
    putStr "Skolemization:  "
    putStrLn $ prettyPrint $ skolem formula
