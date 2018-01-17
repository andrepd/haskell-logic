import Logic.Parser
import Logic.AST

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

prettyPrint :: Formula -> String
prettyPrint f = case f of 
    Val x -> case x of
        True -> "T"
        False -> "False"
    Var x -> x
    Not x -> "~ " ++ prettyPrint x
    And x y -> "(" ++ prettyPrint x ++ " & " ++ prettyPrint y ++ ")"
    Or x y -> "(" ++ prettyPrint x ++ " | " ++ prettyPrint y ++ ")"
    Imp x y -> "(" ++ prettyPrint x ++ " > " ++ prettyPrint y ++ ")"
    Iff x y -> "(" ++ prettyPrint x ++ " = " ++ prettyPrint y ++ ")"

----

main = do
    let exp = parseExpr "x | T &y"
    putStrLn $ show $ exp
    let Right x = exp
    putStrLn $ prettyPrint x
