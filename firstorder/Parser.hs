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
                 -- , opStart = oneOf  ":!#$%&*+/<=>?^|-~∧∨⇒⇔"
                 -- , opLetter = oneOf ":!#$%&*+/<=>?^|-~"
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
e_operator   = Token.operator   e_lexer
e_natural    = Token.natural    e_lexer

-- Formula parser
expr :: Parser Formula
expr = buildExpressionParser e_table form

form = e_parens expr <|> literalTerm <|> quantifier <|> predicate <?> "Error form"

literalTerm = (e_reserved "T" >> return (Val True) )
          <|> (e_reserved "F" >> return (Val False))
          <|> (e_reserved "⊤" >> return (Val True) )
          <|> (e_reserved "⊥" >> return (Val False))
          <?> "Error literalTerm"

quantifier = do { (e_lexeme . oneOf) "@∀";  vars <- many e_identifier; (e_lexeme . char) '.'; form <- expr; return $ foldr Forall form vars } 
         <|> do { (e_lexeme . oneOf) "\\∃"; vars <- many e_identifier; (e_lexeme . char) '.'; form <- expr; return $ foldr Exists form vars }
         <?> "Error quantifier"

-- atom = Atm <$> predicate <?> "Error atom"

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
-- Operator table, from highest to lowest priority
-- f_table = [ [ f_prefix "-" Not, f_prefix "+" Not ]
--           , [ f_binary "&"  And AssocLeft, f_binary "∧" And AssocLeft ]
--           , [ f_binary "|"  Or  AssocLeft, f_binary "∨" Or  AssocLeft ]
--           , [ f_binary "=>" Imp AssocLeft, f_binary "⇒" Imp AssocLeft ]
--           , [ f_binary "==" Iff AssocLeft, f_binary "⇔" Iff AssocLeft ]
--           ]

-- e_binary  name fun = Infix   $ e_operator name >> return fun
-- e_prefix  name fun = Prefix  $ e_operator name >> return fun
-- e_postfix name fun = Postfix $ e_operator name >> return fun


-- Predicate parser
predicate :: Parser Formula
predicate = try (do
                ident <- e_identifier
                terms <- e_parens (e_commaSep term)
                return $ Pred ident terms
                ) 
        <|> (do
            ident <- e_identifier
            return $ Pred ident []
            )
    <?> "Error predicate"



-- Term parser
term :: Parser Term
term = try function
   <|> variable
   <?> "Error term"

variable = Var <$> e_identifier <?> "Error variable"

function = Parser.natural
       <|> (do
           ident <- e_identifier
           terms <- e_parens (e_commaSep term)
           return $ Func ident terms
           )
       <?> "Error function"

-- Integer numbers are interpreted as 0-ary functions (constants) so you don't have to type 123() 
natural = do
    ident <- e_natural
    return $ Func (show ident) []
    

-- Parser
parseExp :: String -> Either ParseError Formula
parseExp = parse expr ""

-- @x. ~eq(x,0) => \y. eq(times(x,y),1)
-- @x. ~(x=0) => \y. x*y=1
