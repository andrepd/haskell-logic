{-# LANGUAGE ParallelListComp #-}

import FOL.Parser
import FOL.AST

import Data.Set (Set)
import Data.Functor
import Data.List (intercalate, nub, sort)
import Data.Function ((&))
import qualified Data.Set as Set

import Debug.Trace(traceShow, traceShowId)
-- traceShow _ = id
-- traceShowId = id

type Valuation obj = String -> obj  -- Variables
type Interpretation obj = ( [obj]                      -- Domain
                          , String -> ([obj] -> obj)   -- Functions
                          , String -> ([obj] -> Bool)  -- Predicates
                          )

-- instance Functor Formula where
-- unmap :: (String -> String) -> Formula -> Formula
-- unmap :: (String -> Formula) -> Formula -> Formula
-- unmap func f = case f of
--     -- Var x -> Var (func x)
--     Atm x -> func x
--     Not x -> Not (unmap func x)
--     And x y -> And (unmap func x) (unmap func y)
--     Or  x y -> Or  (unmap func x) (unmap func y)
--     Imp x y -> Imp (unmap func x) (unmap func y)
--     Iff x y -> Iff (unmap func x) (unmap func y)
--     _ -> f

-- -- instance Foldable Formula where
-- -- binmap :: (a -> b -> b) -> b -> Formula -> b
-- -- binmap func acc f = traceShow (acc, f) $ case f of
-- binmap func acc f = case f of
--     Val x -> acc
--     Var x -> func x acc
--     Not x -> binmap func acc x
--     And x y -> binmap func (binmap func acc x) y
--     Or x y -> binmap func (binmap func acc x) y
--     Imp x y -> binmap func (binmap func acc x) y
--     Iff x y -> binmap func (binmap func acc x) y

prettyPrint :: Formula -> String
prettyPrint f = case f of 
    Val x -> case x of
        True -> "⊤"
        False -> "⊥"
    Atm x -> prettyPrintPred x
    Not x -> "¬" ++ prettyPrint x
    And x y -> "(" ++ prettyPrint x ++ " ∧ " ++ prettyPrint y ++ ")"
    Or x y -> "(" ++ prettyPrint x ++ " ∨ " ++ prettyPrint y ++ ")"
    Imp x y -> "(" ++ prettyPrint x ++ " ⇒ " ++ prettyPrint y ++ ")"
    Iff x y -> "(" ++ prettyPrint x ++ " ⇔ " ++ prettyPrint y ++ ")"
    Forall x p -> "∀" ++ x ++ " . " ++ prettyPrint p
    Exists x p -> "∃" ++ x ++ " . " ++ prettyPrint p
    where
        prettyPrintPred :: Pred -> String
        prettyPrintPred x = case x of
            Pred name terms -> name ++ "(" ++ intercalate "," (map prettyPrintTerm terms) ++ ")"    
        prettyPrintTerm :: Term -> String
        prettyPrintTerm x = case x of
            Var x -> x
            Func name terms -> name ++ "(" ++ intercalate "," (map prettyPrintTerm terms) ++ ")"    



-- subst :: String -> String -> Formula -> Formula
-- subst a b f = case f of
--     Atm x -> substPred x
--     Not x -> Not (subst a b x)
--     And x y -> And (subst a b x) (subst a b y)
--     Or  x y -> Or  (subst a b x) (subst a b y)
--     Imp x y -> Imp (subst a b x) (subst a b y)
--     Iff x y -> Iff (subst a b x) (subst a b y)
--     _ -> f
--     where 
--         substPred p = case p of
--             Pred name terms -> Pred name (map substTerm terms)
--         substTerm t = case t of
--             Var x -> Var $ func x
--             Func name terms -> Func name (map substTerm terms)
--         func s = if a == b then b else s

-- subst :: String -> String -> Valuation obj -> Valuation obj
-- subst a b v x = if x == a then v b else v x

subst :: String -> obj -> Valuation obj -> Valuation obj
subst a b v x = if x == a then b else v x

-- subst :: String -> String -> Formula -> Formula
-- subst a b f = unmap func f where 
--     func x | x == a    = Var b 
--            | otherwise = x

termval :: Interpretation obj -> Valuation obj -> Term -> obj
termval m@(domain, funcInterp, predInterp) v f = case f of
    Var x -> v x
    Func name args -> func (map (termval m v) args) where func = funcInterp name

holds :: Interpretation obj -> Valuation obj -> Formula -> Bool
holds m@(domain, funcInterp, predInterp) v f = case f of
    Val x -> x
    Atm (Pred name args) -> rel (map (termval m v) args) where rel = predInterp name
    Not x -> not (holds m v x)
    And x y -> (holds m v x) && (holds m v y)
    Or  x y -> (holds m v x) || (holds m v y)
    Imp x y -> not (holds m v x) || (holds m v y)
    Iff x y -> (holds m v x) == (holds m v y)
    Forall x p -> all (\a -> holds m (subst x a v) p) domain
    Exists x p -> any (\a -> holds m (subst x a v) p) domain

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
        func "plus"  [x,y] = not $ x == y
        func "times" [x,y] = x && y
        func _ _ = error "Bad function"
        pred "eq" [x,y] = x == y
        pred _ _ = error "Bad predicate"
    in (dom, func, pred)

modNInterp :: Int -> Interpretation Int
modNInterp n =
    let dom = [0..n-1]
        func "0" [] = 0 `mod` n
        func "1" [] = 1 `mod` n
        func "plus"  [x,y] = (x+y) `mod` n
        func "times" [x,y] = (x*y) `mod` n
        func _ _ = error "Bad function"
        pred "eq" [x,y] = x == y
        pred _ _ = error "Bad predicate"
    in (dom, func, pred)



main = do
    -- inp <- getLine
    -- putLn
    -- let formula = (extract . parseExp) inp
    -- putStrLn $ show $ formula

    let formula1 = (extract . parseExp) "@x . eq(x,0()) | eq(x,1())"
    putStrLn $ show $ holds boolInterp undefined formula1
    putStrLn $ show $ holds (modNInterp 2) undefined formula1
    putStrLn $ show $ holds (modNInterp 3) undefined formula1
    putLn

    let formula2 = (extract . parseExp) "@x. ~eq(x,0()) => \\y. eq(times(x,y),1())"
    putStrLn $ show $ filter (\n -> holds (modNInterp n) undefined formula2) [1..50]
