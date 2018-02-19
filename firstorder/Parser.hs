module Parser(parseExp) where

import AST
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token as Token
import Text.Parsec.Language
-- import qualified Text.Parsec.Lexer as L

-- import Debug.Trace(trace)
trace _ = id

-- Language definition
e_def = emptyDef { identStart = letter
                 , identLetter = alphaNum <|> char '\''
                 , opStart = oneOf "&|>=~∧∨⇒⇔"
                 , opLetter = oneOf ">="
                 , reservedOpNames = ["&", "|", "=>", "==", "~", "∧", "∨", "⇒", "⇔"]
                 , reservedNames = ["T","F"]
                 }

-- Lexer based on that definition
e_lexer = makeTokenParser e_def

-- Elementary parsers
e_parens     = Token.parens     e_lexer
e_reserved   = Token.reserved   e_lexer
e_reservedOp = Token.reservedOp e_lexer
e_identifier = Token.identifier e_lexer
e_commaSep   = Token.commaSep   e_lexer
e_lexeme     = Token.lexeme     e_lexer
e_whiteSpace = Token.whiteSpace e_lexer

-- Formula parser
expr :: Parser Formula
expr = buildExpressionParser e_table form

form = e_parens expr <|> literalTerm <|> quantifier <|> predicate <?> "Error form"

literalTerm = (e_reserved "T" >> (return $ Val True ))
          <|> (e_reserved "F" >> (return $ Val False))
          <|> (e_reserved "⊤" >> (return $ Val True ))
          <|> (e_reserved "⊥" >> (return $ Val False))
          <?> "Error literalTerm"

quantifier = do { (e_lexeme . oneOf) "@ ∀"; vars <- many e_identifier; (e_lexeme . char) '.'; form <- expr; return $ foldr Forall form vars } 
         <|> do { (e_lexeme . oneOf) "\\∃"; vars <- many e_identifier; (e_lexeme . char) '.'; form <- expr; return $ foldr Exists form vars }
         <?> "Error quantifier"

-- Operator table, from highest to lowest priority
e_table = [ [ e_prefix "~" Not, e_prefix "¬" Not ]
          , [ e_binary "&"  And AssocLeft, e_binary "∧" And AssocLeft ]
          , [ e_binary "|"  Or  AssocLeft, e_binary "∨" Or  AssocLeft ]
          , [ e_binary "=>" Imp AssocLeft, e_binary "⇒" Imp AssocLeft ]
          , [ e_binary "==" Iff AssocLeft, e_binary "⇔" Iff AssocLeft ]
          ]

e_binary  name fun = Infix   $ e_reservedOp name >> return fun
e_prefix  name fun = Prefix  $ e_reservedOp name >> return fun
e_postfix name fun = Postfix $ e_reservedOp name >> return fun



-- Relations/Functions --

-- Predicate parser
predicate :: Parser Formula
-- predicate = buildExpressionParser (f_table Pred) predicate'
predicate = try rel <|> predicate'

-- Infix notation for relations
rel = do
    term1 <- term
    op <- choice $ map (try . string) ["<=", ">=", "<", ">", "=", "/=", "≤", "≥", "≠"]
    term2 <- term
    return $ Pred (opTranslationTable op) [term1, term2]

-- Translates operators to synonyms
opTranslationTable op | op `elem` ["<=", "≤"] = "≤"
                      | op `elem` [">=", "≥"] = "≥"
                      | op `elem` ["/=", "≠"] = "≠"
                      | otherwise = op

-- predicate' :: Parser Formula
predicate' = try funcPredicate <|> constPredicate <?> "Error predicate"

funcPredicate = do
    ident <- e_identifier
    terms <- e_parens (e_commaSep term)
    return $ Pred ident terms

constPredicate = do
    ident <- e_identifier
    return $ Pred ident []            



-- Term parser
t_def = emptyDef { identStart = letter  -- <|> oneOf "+-*/*"
                 , identLetter = alphaNum <|> oneOf "\'_"
                 , opStart = oneOf  ":!#$%&*+/<=>?^|-~"
                 , opLetter = oneOf ":!#$%&*+/<=>?^|-~"
                 , reservedOpNames = ["-", "+", "^", "*", "/"]
                 }

-- Lexer based on that definition
t_lexer = makeTokenParser t_def

-- Elementary parsers
t_parens     = Token.parens     t_lexer
t_reservedOp = Token.reservedOp t_lexer
t_identifier = Token.identifier t_lexer
t_commaSep   = Token.commaSep   t_lexer
t_natural    = Token.natural    t_lexer

-- Operator table, from highest to lowest priority
t_table = [ [ t_prefix "-", t_prefix "+" ]
          , [ t_binary "^" AssocLeft ]
          , [ t_binary "*" AssocLeft, t_binary "/"  AssocLeft ]
          , [ t_binary "+" AssocLeft, t_binary "-"  AssocLeft ]
          -- , [ t_binary "=" AssocLeft, t_binary "/=" AssocLeft ]
          -- , [ t_binary "<" AssocLeft, t_binary ">"  AssocLeft, t_binary "<=" AssocLeft, t_binary "<=" AssocLeft ]
          ]

t_binary  name = Infix   $ t_reservedOp name >> return (\x y -> Func name [x,y])
t_prefix  name = Prefix  $ t_reservedOp name >> return (\x   -> Func name [x]  )
t_postfix name = Postfix $ t_reservedOp name >> return (\x   -> Func name [x]  )



term :: Parser Term
term = buildExpressionParser t_table term'
-- term = naturalTerm <|> try funcTerm <|> variable <?> "Error term"

term' = t_parens term <|> naturalTerm <|> try funcTerm <|> variable <?> "Error term"

variable = Var <$> e_identifier <?> "Error variable"

funcTerm = do
    ident <- t_identifier
    terms <- t_parens (t_commaSep term)
    return $ Func ident terms
    -- <?> "Error funcTerm"

-- Integer numbers are interpreted as 0-ary functions (constants) so you don't have to type 123() 
naturalTerm = do
    ident <- t_natural
    return $ Func (show ident) []
    

-- Parser
parseExp :: String -> Either ParseError Formula
parseExp = parse expr ""

-- @x. ~eq(x,0) => \y. eq(times(x,y),1)
-- @x. ~(x=0) => \y. x*y=1
