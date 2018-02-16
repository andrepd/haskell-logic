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
                 , identLetter = alphaNum
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
expr = buildExpressionParser table form

form = e_parens expr <|> literalTerm <|> quantifier <|> atom <?> "Error form"

literalTerm = (e_reserved "T" >> return (Val True) )
          <|> (e_reserved "F" >> return (Val False))
          <|> (e_reserved "⊤" >> return (Val True) )
          <|> (e_reserved "⊥" >> return (Val False))
          <?> "Error literalTerm"

quantifier = do { (e_lexeme . char) '@';  var <- e_identifier; (e_lexeme . char) '.'; form <- expr; return $ Forall var form } 
         <|> do { (e_lexeme . char) '\\'; var <- e_identifier; (e_lexeme . char) '.'; form <- expr; return $ Exists var form }
         <?> "Error quantifier"

atom = Atm <$> predicate <?> "Error atom"

-- Operator table, from highest to lowest priority
table = [ [ prefix "~" Not, prefix "¬" Not ]
        , [ binary "&"  And AssocLeft, binary "∧" And AssocLeft ]
        , [ binary "|"  Or  AssocLeft, binary "∨" Or  AssocLeft ]
        , [ binary "=>" Imp AssocLeft, binary "⇒" Imp AssocLeft ]
        , [ binary "==" Iff AssocLeft, binary "⇔" Iff AssocLeft ]
        ]

binary  name fun = Infix   (e_reservedOp name >> return fun)
prefix  name fun = Prefix  (e_reservedOp name >> return fun)
postfix name fun = Postfix (e_reservedOp name >> return fun)



-- Predicate parser
predicate :: Parser Pred
predicate = (do
    ident <- e_identifier
    terms <- e_parens (e_commaSep term)
    return $ Pred ident terms
    ) 
    <?> "Error predicate"



-- Term parser
term :: Parser Term
term = try (trace "a" function)
   <|> variable
   <?> "Error term"

variable = Var <$> (trace "b" $ e_identifier) <?> "Error variable"

function = Parser.natural
    <|> (do
        ident <- trace "bb" e_identifier
        terms <- e_parens (e_commaSep term)
        return $ trace "b" $ Func ident terms
        )
    <?> "Error function"

-- Integer numbers are interpreted as 0-ary functions (constants) so you don't have to type 123() 
natural = do
    ident <- trace "cc" e_natural
    return $ trace "c" $ Func (show ident) []
    

-- Parser
parseExp :: String -> Either ParseError Formula
parseExp = parse expr ""

-- @x. ~eq(x,0) => \y. eq(times(x,y),1)
-- @x. ~(x=0) => \y. x*y=1
