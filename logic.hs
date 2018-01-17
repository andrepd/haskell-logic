{-# LANGUAGE ParallelListComp #-}

import Logic.Parser
import Logic.AST

import Data.Set (Set)
import Data.Functor
import Data.List

import Debug.Trace(traceShow, traceShowId)

-- TODO make monadic (Maybe)
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
--     fmap func f = case f of
--         Var x -> Var func x
--         Not x -> Not (fmap func x)
--         And x y -> And (fmap func x) (fmap func y)
--         Or x y -> Or (fmap func x) (fmap func y)
--         Imp x y -> Imp (fmap func x) (fmap func y)
--         Iff x y -> Iff (fmap func x) (fmap func y)
--         _ -> f
unmap func f = case f of
    Var x -> Var (func x)
    Not x -> Not (unmap func x)
    And x y -> And (unmap func x) (unmap func y)
    Or x y -> Or (unmap func x) (unmap func y)
    Imp x y -> Imp (unmap func x) (unmap func y)
    Iff x y -> Iff (unmap func x) (unmap func y)
    _ -> f

-- instance Applicative Formula where
--     pure 
--     liftA2 
-- binmap :: (a -> a -> a) -> a -> Formula -> a
binmap func acc f = traceShow (acc, f) $ case f of
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
        True -> "T"
        False -> "F"
    Var x -> x
    Not x -> "~ " ++ prettyPrint x
    And x y -> "(" ++ prettyPrint x ++ " & " ++ prettyPrint y ++ ")"
    Or x y -> "(" ++ prettyPrint x ++ " | " ++ prettyPrint y ++ ")"
    Imp x y -> "(" ++ prettyPrint x ++ " > " ++ prettyPrint y ++ ")"
    Iff x y -> "(" ++ prettyPrint x ++ " = " ++ prettyPrint y ++ ")"



alistToFunc :: (Eq a) => [(a,b)] -> (a -> b)
alistToFunc [] _ = error "Key miss"
alistToFunc ((key,val):xs) x = if key == x then val else alistToFunc xs x

-- truthTable :: Formula -> String
-- truthTable f = [ eval v f | v <- valuations tokens ]
--     where valuations = [  ]
--           tokens = getTokens f

truthTable :: Formula -> String
truthTable f = let tokens = getTokens f
                   vals = possibleValuations tokens
                   -- rows = map (\l -> map snd l) vals
                   rows = map (map snd) vals
                   valsAsFuncs = map alistToFunc vals
                   res = [eval f v | v <- valsAsFuncs]

                   show' x = case x of
                       True -> "T"
                       False -> "F"
                   nDashes = 2*(length $ head rows) + 3
               -- in show rows ++ "\n" ++ show res ++ "\n" ++ show tokens
               -- in intersperse "    " [show rows, show res, show tokens]
               in intercalate " " tokens ++ "\n"
                  -- ++ "--------\n"
                  ++ replicate nDashes '-' ++ "\n"
                  -- ++ intercalate "\n" (map (intercalate " ") (map (map show) rows)) 
                  ++ intercalate "\n" [ row ++ " | " ++ result | row <- map (intercalate " ") (map (map show') rows) | result <- map show' res ]

{-
["y"]
[ [ (y,True) ], [ (y,False) ] ]
-}

possibleValuations :: [String] -> [[(String,Bool)]]
possibleValuations [] = [[]]
-- possibleValuations (x:xs) = ((x, True):(possibleValuations xs)):((x, False):(possibleValuations xs)):xs
-- possibleValuations (x:xs) = ((x, True):[ head x | x <- (possibleValuations xs)]):((x, False):(possibleValuations xs)):xs
-- possibleValuations (x:xs) = let res = [(x, True):v | v <- possibleValuations xs] ++ [(x, False):v | v <- possibleValuations xs]
--                             in traceShow (x,xs,res) res
-- possibleValuations (x:xs) = let res = [(x,True):v | v <- valsxs] ++ [(x,False):v | v <- valsxs] where valsxs = possibleValuations xs
--                             in traceShow (x,xs,res) res
possibleValuations (x:xs) = [(x,True):v | v <- valsxs] ++ [(x,False):v | v <- valsxs] where valsxs = possibleValuations xs



getTokens :: Formula -> [String]
getTokens = binmap (:) []
-- getTokens = binmap (\x y -> [x] ++ y) []
-- getTokens = binmap (++) []
-- getTokens f = case f of
--     Val x -> []
--     Var x -> [x]
--     Not x -> getTokens x
--     And x y -> getTokens x ++ getTokens y
--     Or x y -> getTokens x ++ getTokens y
--     Imp x y -> getTokens x ++ getTokens y
--     Iff x y -> getTokens x ++ getTokens y

----

main = do
    let parserResult = parseExpr "(x | F)&y"
    let Right exp = parserResult
    putStrLn $ show $ exp
    putStrLn $ prettyPrint exp
    let tokens = getTokens exp
    putStrLn $ show $ tokens
    putStrLn $ show $ possibleValuations tokens
    -- putStrLn $ show $ possibleValuations ["x"]
    putStrLn $ truthTable exp
