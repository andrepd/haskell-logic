{-# LANGUAGE ParallelListComp #-}

import PropLogic.Parser
import PropLogic.AST

import Data.Set (Set)
import Data.Functor
import Data.List (intercalate, nub, sort)
-- import Data.Either
import Data.Function ((&))
import qualified Data.Set as Set
import Data.Foldable
import Data.Ord (comparing)

import Debug.Trace(trace, traceShow, traceShowId)
-- traceShow _ = id
-- traceShowId = id

type Valuation = String -> Bool

eval :: Formula -> Valuation -> Bool
eval f v = case f of
    Val x -> x
    Var x -> v x
    Not x -> not $ eval x v
    And x y -> eval x v && eval y v
    Or x y -> eval x v || eval y v
    Imp x y -> not (eval x v) || eval y v
    Iff x y -> eval x v == eval y v



-- instance Functor Formula where
-- unmap :: (String -> String) -> Formula -> Formula
unmap :: (String -> Formula) -> Formula -> Formula
unmap func f = case f of
    -- Var x -> Var (func x)
    Var x -> func x
    Not x -> Not (unmap func x)
    And x y -> And (unmap func x) (unmap func y)
    Or  x y -> Or  (unmap func x) (unmap func y)
    Imp x y -> Imp (unmap func x) (unmap func y)
    Iff x y -> Iff (unmap func x) (unmap func y)
    _ -> f

-- instance Foldable Formula where
-- binmap :: (a -> b -> b) -> b -> Formula -> b
-- binmap func acc f = traceShow (acc, f) $ case f of
binmap func acc f = case f of
    Val x -> acc
    Var x -> func x acc
    Not x -> binmap func acc x
    And x y -> binmap func (binmap func acc x) y
    Or x y -> binmap func (binmap func acc x) y
    Imp x y -> binmap func (binmap func acc x) y
    Iff x y -> binmap func (binmap func acc x) y



prettyPrint :: Formula -> String
prettyPrint f = case f of 
    Val x -> case x of
        True -> "⊤"
        False -> "⊥"
    Var x -> x
    Not x -> "¬" ++ prettyPrint x
    And x y -> "(" ++ prettyPrint x ++ " ∧ " ++ prettyPrint y ++ ")"
    Or x y -> "(" ++ prettyPrint x ++ " ∨ " ++ prettyPrint y ++ ")"
    Imp x y -> "(" ++ prettyPrint x ++ " ⇒ " ++ prettyPrint y ++ ")"
    Iff x y -> "(" ++ prettyPrint x ++ " ⇔ " ++ prettyPrint y ++ ")"

instance Show Formula where
    show f = "parseExp \"" ++ prettyPrint f ++ "\""



-- Helper function, turns association list to function
alistToFunc :: (Eq a) => [(a,b)] -> (a -> b)
alistToFunc [] _ = error "Key miss"
alistToFunc ((key,val):xs) x = if key == x then val else alistToFunc xs x
-- alistToFunc list elem = 

-- Prints a truth table for a given formula
truthTable :: Formula -> String
truthTable f = let atoms = getAtoms f
                   vals = possibleValuations' atoms
                   rows = map (map snd) vals
                   valsAsFuncs = map alistToFunc vals
                   results = possibleResults f valsAsFuncs

                   show' x = case x of
                       True -> "T"
                       False -> "F"
                   nDashes = 2*(length $ head rows) + 3

                   rows' = map (intercalate " ") (map (map show') rows)
                   results' = map show' results
               in intercalate " " atoms ++ " | " ++ prettyPrint f ++ "\n"
                  ++ replicate nDashes '-' ++ "\n"
                  ++ intercalate "\n" [ row ++ " | " ++ result | row <- rows' | result <- results' ] ++ "\n"

-- Generates all possible valuations of a given formula
possibleValuations :: Formula -> [Valuation]
possibleValuations = map alistToFunc . possibleValuations' . getAtoms

-- Generates all possible combinations of (identifier,True/False) from a list of identifiers
possibleValuations' :: [String] -> [[(String,Bool)]]
possibleValuations' [] = [[]]
possibleValuations' (x:xs) = [(x,True):v | v <- valsxs] ++ [(x,False):v | v <- valsxs] where valsxs = possibleValuations' xs

-- Maps eval f to vals
possibleResults :: Formula -> [Valuation] -> [Bool]
possibleResults f vals = map (eval f) vals
-- possibleResults f vals = [eval f v | v <- vals]

-- Gets a list of all (unique) atoms 
getAtoms :: Formula -> [String]
getAtoms = sort . nub . binmap (:) []



-- Checks if a formula is a tautology (true in all valuations), a contradiction (false in all valuations), or satisfiable (true in some valuation)
tautology, satisfiable, contradiction :: Formula -> Bool
tautology f = and (possibleResults f $ possibleValuations f)
satisfiable f = not $ contradiction f
contradiction f = tautology $ Not f

-- Checks if two formulae are equivalent (a ⇔ b)
equivalent :: Formula -> Formula -> Bool
equivalent a b = tautology $ Iff a b



-- Returns the dual of a formula (replacing constants by their negation, and Ands by Ors). Fails if formula has implication or equivalence connectives
dual :: Formula -> Formula
dual f = case f of
    Val x -> Val (not x)
    Var x -> f
    Not x -> Not (dual x)
    And x y -> Or (dual x) (dual y)
    Or x y -> And (dual x) (dual y)
    _ -> error "The formula involves implication and/or equivalence connectives"



-- Simplifies a formula by removing constants and double negation
simplify :: Formula -> Formula
simplify f = let
    simplify' f = case f of
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
        _ -> f
    in case f of
        Not x -> simplify' $ Not (simplify x)
        And x y -> simplify' $ And (simplify x) (simplify y)
        Or  x y -> simplify' $ Or  (simplify x) (simplify y)
        Imp x y -> simplify' $ Imp (simplify x) (simplify y)
        Iff x y -> simplify' $ Iff (simplify x) (simplify y)
        _ -> f



-- TODO allow simultaneous substitutions by substituting in first pass x -> y_TEMP and then y_TEMP -> y
subst :: [String -> Formula] -> Formula -> Formula
subst [] f = f
subst (x:xs) f = unmap x (subst xs f)



positive :: Formula -> Bool
positive p = case p of
    Not x -> False
    x     -> True

negateTerm :: Formula -> Formula
negateTerm p = case p of
    Not x -> x
    x -> Not x

-- A literal is a constant or an atom
literal :: Formula -> Bool
literal f = case f of
    Val x -> True
    Var x -> True
    _ -> False



-- Negation Normal Form
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
    _ -> f

-- NNF after simplify
nnf = nnf' . simplify

-- Negation-Equivalence Normal Form
nenf' f = case f of
    Not (Not x) -> nenf' x
    Not (And x y) -> Or  (nenf' $ Not x) (nenf' $ Not y)
    Not (Or  x y) -> And (nenf' $ Not x) (nenf' $ Not y)
    Not (Imp x y) -> And (nenf' x) (nenf' $ Not y)
    Not (Iff x y) -> Iff (nenf' x) (nenf' $ Not y)
    And x y -> And (nenf' x) (nenf' y)
    Or  x y -> Or  (nenf' x) (nenf' y)
    Imp x y -> Or (nenf' $ Not x) (nenf' y)
    Iff x y -> Iff (nenf' x) (nenf' y)
    _ -> f

-- NENF after simplify
nenf = nenf' . simplify



-- Maps list of formulas to their conjunction
listToConj :: [Formula] -> Formula
listToConj [] = Val True  -- Trivial case
listToConj (x:[]) = x
listToConj (x:xs) = And x (listToConj xs)

-- Maps list of formulas to their disjunction
listToDisj :: [Formula] -> Formula
listToDisj [] = Val False  -- Trivial case
listToDisj (x:[]) = x
listToDisj (x:xs) = Or x (listToDisj xs)

-- Given a list of formulas and a valuation, return a conjunction of formulas where each formula is: mapped to itself if it is true in that valuation, or mapped to its negation if it is false in that valuation
-- The result is a conjunction that is true under any valuation that agrees with valuation v
listToValConj :: [Formula] -> Valuation -> Formula
listToValConj lf v = listToConj $ map aux lf where
    aux x = case eval x v of
        True -> x
        False -> Not x

-- Disjunction Normal Form
-- Strategy to calculate: 
--   get rows/valuations of the truth table that satisfy the formula; 
--   for each row/valuation, the corresponding term is a conjunction of each atom where: the atom is unchanged if the atom is true in that valuation, or negated if it is false in that valuation;
--   DNF is the disjunction of those terms, one for each row that satisfies the formula
-- This shows how the dnf is basically the truth table cast in a different form
{- dnf :: Formula -> Formula
dnf f = let atoms = getAtoms f
            vals = possibleValuations f
            satvals = filter (eval f) vals
        in listToDisj $ map (listToValConj (map Var atoms)) satvals -}



-- Disjunction Normal Form: set-based approach
-- A formula in DNF is represented by a set of sets, i.e. {{a,b},{c,d,e}} = (a∧b)∨(c∧d∧e)
-- Likewise, a formula in CNF is represented by a set of sets, i.e. {{a,b},{c,d,e}} = (a∨b)∧(c∨d∨e)
type SetNF = Set (Set Formula)

-- Conjuntion of two formulas in DNF as represented by sets 
distrib :: SetNF -> SetNF -> SetNF
distrib a b = Set.fromList [ Set.unions [i,j] | i <- Set.elems a, j <- Set.elems b ]

-- Convert formula to set DNF (first put into NNF)
setdnf :: Formula -> SetNF
setdnf = setdnf' . nnf where
    setdnf' f = case f of
        And x y -> distrib (setdnf' x) (setdnf' y)
        Or  x y -> Set.union (setdnf' x) (setdnf' y)
        _ -> Set.singleton (Set.singleton (f))

-- Any conjunction with p and ¬p in its terms is trivially ⊥ so it can be removed from the disjunction
setdnfRemoveTrivial :: SetNF -> SetNF
setdnfRemoveTrivial s = Set.filter aux s where
    aux s = let (pos,neg) = Set.partition positive s
            in null $ Set.intersection (pos) (Set.map negateTerm neg)

-- If a conjunction is ''a subset of'' another, then in a valuation where the latter is satisfiable the former also is. Therefore we can remove the former from the disjunction
setdnfRemoveSubsumptions :: SetNF -> SetNF
setdnfRemoveSubsumptions s = Set.filter aux s where
    aux x = not $ any (`Set.isProperSubsetOf` x) s

-- Set DNF with simplifications
setdnfSimplify :: Formula -> SetNF
setdnfSimplify = setdnfRemoveSubsumptions . setdnfRemoveTrivial . setdnf

setdnfToFormula :: SetNF -> Formula
setdnfToFormula f = if null f
    then Val False
    else setFoldr1 Or $ Set.map (\x -> if null x then Val True else setFoldr1 And x) f
    where setFoldr1 f = foldr1 f . Set.elems

-- Alternative definition of DNF from set DNF
dnf :: Formula -> Formula
dnf = setdnfToFormula . setdnfSimplify



-- Conjunction Normal Form
-- Apply de Morgan's laws to go from DNF to CNF
setcnf :: Formula -> SetNF
setcnf f = Set.map (Set.map negateTerm) (setdnf $ Not f)

-- Any disjunction with p and ¬p in its terms is trivially ⊤ so it can be removed from the conjunction
setcnfRemoveTrivial :: SetNF -> SetNF
setcnfRemoveTrivial = setdnfRemoveTrivial

setcnfRemoveSubsumptions :: SetNF -> SetNF
setcnfRemoveSubsumptions = setdnfRemoveSubsumptions

setcnfSimplify :: Formula -> SetNF
setcnfSimplify = setcnfRemoveSubsumptions . setcnfRemoveTrivial . setcnf

setcnfToFormula :: SetNF -> Formula
setcnfToFormula f = if null f
    then Val True
    else setFoldr1 And $ Set.map (\x -> if null x then Val False else setFoldr1 Or x) f
    where setFoldr1 f = foldr1 f . Set.elems

cnf :: Formula -> Formula
cnf = setcnfToFormula . setcnfSimplify


-- Print formulas in DNF/CNF without distracting parentheses
prettyPrintDNF :: Formula -> String
prettyPrintDNF f = "(" ++ prettyPrintDNF' f ++ ")" where
    prettyPrintDNF' f = case f of 
        Val x -> case x of
            True -> "⊤"
            False -> "⊥"
        Var x -> x
        Not x -> "¬" ++ prettyPrintDNF' x
        And x y -> prettyPrintDNF' x ++ " ∧ " ++ prettyPrintDNF' y
        Or x y -> prettyPrintDNF' x ++ ") ∨ (" ++ prettyPrintDNF' y
        Imp x y -> prettyPrintDNF' x ++ " ⇒ " ++ prettyPrintDNF' y
        Iff x y -> prettyPrintDNF' x ++ " ⇔ " ++ prettyPrintDNF' y

prettyPrintCNF :: Formula -> String
prettyPrintCNF f = "(" ++ prettyPrintCNF' f ++ ")" where
prettyPrintCNF' f = case f of 
    Val x -> case x of
        True -> "⊤"
        False -> "⊥"
    Var x -> x
    Not x -> "¬" ++ prettyPrintCNF' x
    And x y -> prettyPrintCNF' x ++ ") ∧ (" ++ prettyPrintCNF' y
    Or x y -> prettyPrintCNF' x ++ " ∨ " ++ prettyPrintCNF' y
    Imp x y -> prettyPrintCNF' x ++ " ⇒ " ++ prettyPrintCNF' y
    Iff x y -> prettyPrintCNF' x ++ " ⇔ " ++ prettyPrintCNF' y

prettyPrintSetDNF :: SetNF -> String
prettyPrintSetDNF f = intercalate " ∨ " . map (\x -> "("++x++")") . Set.elems $ Set.map (intercalate " ∧ " . Set.elems . (Set.map prettyPrint)) f
    -- where 
    --     aux y = case y of
    --         Var x -> x
    --         _ -> error "Invalid setDNF"

prettyPrintSetCNF :: SetNF -> String
prettyPrintSetCNF f = intercalate " ∧ " . map (\x -> "("++x++")") . Set.elems $ Set.map (intercalate " ∨ " . Set.elems . (Set.map prettyPrint)) f
    -- where 
    --     aux y = case y of
    --         Var x -> x
    --         _ -> error "Invalid setCNF"



-- Definitional CNF
-- Helper function, given a number N yields "p_N" and the next number
mkPropName :: Int -> (String, Int)
mkPropName n = ("p_" ++ show n, n+1)

-- "Core" of the defCNF function. This is applied to a formula in NENF. Maintains state in the form of an association-list of definitions and the number N for the next definitional variable name
maindefcnf :: (Formula, [(Formula, String)], Int) -> (Formula, [(Formula, String)], Int)
maindefcnf trip@(f, defs, n) = case f of
    And x y -> defstep And (x,y) trip
    Or  x y -> defstep Or  (x,y) trip
    Iff x y -> defstep Iff (x,y) trip
    _ -> trip
  where 
    defstep op (p,q) (f, defs, n) = 
        let -- Left-hand side
            (f1, defs1, n1) = maindefcnf (p, defs,  n )
            -- Right-hand side
            (f2, defs2, n2) = maindefcnf (q, defs1, n1)
            -- Join left- and right-hand sides
            f' = op f1 f2
            -- Lookup f' in definitions
            name = lookup f' defs
        in case name of
            -- Formula already in defs
            Just v -> (Var v, defs2, n2)
            -- New definition
            Nothing -> let (v, n3) = mkPropName n2
                       in (Var v, (f',v):defs2, n3)

-- Optimization: step through as many conjunctions as possible, then through as many disjunctions as possible, to avoid working on stuff that is already in CNF, then do main
optdefcnfAnd trip@(f, defs, n) = case f of
    And x y -> defstep And (x,y) trip
    _ -> optdefcnfOr trip
  where
    defstep op (x,y) (f, defs, n) =
        let (f1, defs1, n1) = optdefcnfAnd (x, defs,  n )
            (f2, defs2, n2) = optdefcnfAnd (y, defs1, n1)
            f' = op f1 f2
        in (f', defs2, n2)

optdefcnfOr trip@(f, defs, n) = case f of
    Or x y -> defstep Or (x,y) trip
    _ -> maindefcnf trip
  where
    defstep op (x,y) (f, defs, n) =
        let (f1, defs1, n1) = optdefcnfOr (x, defs,  n )
            (f2, defs2, n2) = optdefcnfOr (y, defs1, n1)
            f' = op f1 f2
        in (f', defs2, n2)

-- Given the result of a maindefcnf pass, yields the conjunction of f and the definitions in defs (themselves converted to CNF)
defcnfToFormula :: (Formula, [(Formula, String)], Int) -> Formula
-- defcnfToFormula (f, defs, _) = And f rest
--     where rest = foldr1 And (map cnf (map (\(x,y) -> Iff (Var y) x) defs))
defcnfToFormula (f, defs, _) = case defs of
    [] -> f
    _  -> And f rest
        where rest = foldr1 And (map cnf (map (\(x,y) -> Iff (Var y) x) defs))

-- Same but yields set representation
defcnfToSet :: (Formula, [(Formula, String)], Int) -> SetNF
defcnfToSet (f, defs, _) = case defs of
    [] -> setcnfSimplify f
    _  -> Set.union (setcnfSimplify f) rest
        where rest = Set.unions $ map setcnfSimplify (map (\(x,y) -> Iff (Var y) x) defs)

-- -- Helper function: finds smallest N so that there isn't any variable named p_n with n>=N
-- helper f =
--     let atoms = getAtoms f
--         a' = filter ("p_" `isPrefixOf`) atoms
--         a'' = map (drop 2) a'

defcnf :: Formula -> Formula
-- defcnf f = defcnfToFormula $ maindefcnf (nenf f, [], 1)
defcnf f = defcnfToFormula $ optdefcnfAnd (nenf f, [], 1)  -- Optimised version

setdefcnf :: Formula -> SetNF
-- setdefcnf f = defcnfToSet $ maindefcnf (nenf f, [], 1)
setdefcnf f = defcnfToSet $ optdefcnfAnd (nenf f, [], 1)  -- Optimised version



-- DPLL --

-- 1-unit rule
dpll1unit :: SetNF -> SetNF
dpll1unit f | trace ("1unit " ++ prettyPrintSetCNF f) False = undefined
dpll1unit f = 
    let units = Set.filter (\x -> Set.size x == 1) f
        u = head $ Set.elems $ head $ Set.elems units
        u' = negateTerm u
        -- For each unit u, remove instances of -u from each clause
        f' = Set.map (Set.delete u') f
        -- For each unit u, remove clauses that contain u
        f'' = Set.filter (\x -> not $ (u `Set.member` x)) f'
    in if null units
           then f
           else dpll1unit f''
    
-- Affirmative-negative rule
dpllAffNeg :: SetNF -> SetNF
dpllAffNeg f | trace ("affneg " ++ prettyPrintSetCNF f) False = undefined
dpllAffNeg f = 
    let lits = Set.unions $ Set.elems f
        (pos,neg) = Set.partition positive $ lits
        nonpure = Set.intersection pos (Set.map negateTerm neg)
        pure = Set.difference pos nonpure
    in if null pure
           then f
           else dpllAffNeg $ Set.filter (\x -> null $ Set.intersection pure x) f 

-- -- Splitting rule
-- dpllSplit :: SetNF -> SetNF
-- dpllSplit f = 

dpll :: SetNF -> Bool
dpll f | trace ("dpll " ++ prettyPrintSetCNF f) False = undefined
dpll f = 
    let f' = dpll1unit f  
        f'' = dpllAffNeg f'

        lits = traceShowId $ Set.filter positive $ Set.unions $ Set.elems f''
        p = Data.Foldable.maximumBy (comparing (\x -> count x f'')) lits

        count :: Formula -> SetNF -> Int
        count x f = (Set.size $ Set.filter (x `Set.member`) f) + (Set.size $ Set.filter (negateTerm x `Set.member`) f)

    in if null f || null f' || null f''
          then True
          else if any null (Set.elems f) || any null (Set.elems f') || any null (Set.elems f'')
              then False
              else dpll (Set.insert (Set.singleton p) f'') || dpll (Set.insert (Set.singleton $ negateTerm p) f'')

satisfiableDPLL, tautologyDPLL :: Formula -> Bool
satisfiableDPLL = dpll . setdefcnf
tautologyDPLL = not . satisfiableDPLL . Not

----

extract (Right x) = x
extract (Left _) = error "Parsing error"

putLn = putStrLn ""

boolToSign True  = "✓"
boolToSign False = "✗"

main = do
    inp <- getLine
    putLn
    let formula = (extract . parseExp) inp
    let table = truthTable formula
    putStrLn table

    putStrLn $ "Tautology     " ++ (boolToSign $ tautology     formula)
    putStrLn $ "Satisfiable   " ++ (boolToSign $ satisfiable   formula)
    putStrLn $ "Contradiction " ++ (boolToSign $ contradiction formula)
    putLn

    let formula_simp = simplify formula
    putStrLn "Simplified form:"
    putStrLn $ prettyPrint formula_simp
    putStrLn $ if equivalent formula formula_simp then "Equivalent" else "Not equivalent!"
    putLn

    let formula_dnf = dnf formula
    putStrLn "DNF form:"
    -- putStrLn $ prettyPrintDNF $ (nnf) formula
    -- putStrLn $ prettyPrintDNF $ (setdnfToFormula . setdnf . nnf) formula
    -- putStrLn $ prettyPrintDNF $ (setdnfToFormula . setdnfRemoveTrivial . setdnf . nnf) formula
    -- putStrLn $ prettyPrintDNF $ (setdnfToFormula . setdnfRemoveSubsumptions . setdnfRemoveTrivial . setdnf . nnf) formula
    putStrLn $ prettyPrintDNF formula_dnf
    putStrLn $ if equivalent formula formula_dnf then "Equivalent" else "Not equivalent!"
    putLn

    let formula_cnf = cnf formula
    putStrLn "CNF form:"
    putStrLn $ prettyPrintCNF formula_cnf
    putStrLn $ if equivalent formula formula_cnf then "Equivalent" else "Not equivalent!"
    putLn

    let formula_nenf = nenf formula
    putStrLn "NENF"
    putStrLn $ prettyPrint formula_nenf
    putStrLn $ if equivalent formula formula_nenf then "Equivalent" else "Not equivalent!"
    putLn

    let formula_dcnf = defcnf formula
    putStrLn "Definitional CNF (optimised)"
    putStrLn $ prettyPrintCNF $ formula_dcnf
    -- putStrLn $ prettyPrintCNF $ setcnfToFormula $ setdefcnf formula
    -- putStrLn $ show $ setdefcnf formula
    -- putStrLn $ if equivalent formula formula_dcnf then "Equivalent" else "Not equivalent!"
    putLn

    putStrLn $ "Satisfiable: " ++ (show $ satisfiableDPLL formula)

