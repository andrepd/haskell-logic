module FOL.Parser(parseExp) where

import FOL.AST
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token as Token
import Text.Parsec.Language
-- import qualified Text.Parsec.Lexer as L

-- Language definition
m_def = emptyDef { identStart = alphaNum
                 , identLetter = alphaNum
                 , opStart = oneOf "&|>=~∧∨⇒⇔"
                 , opLetter = oneOf ">="
                 , reservedOpNames = ["&", "|", "=>", "==", "~", "∧", "∨", "⇒", "⇔"]
                 , reservedNames = ["T","F"]
                 }

-- Lexer based on that definition
m_lexer = makeTokenParser m_def

-- Elementary parsers
m_parens     = Token.parens     m_lexer
m_reserved   = Token.reserved   m_lexer
m_reservedOp = Token.reservedOp m_lexer
m_identifier = Token.identifier m_lexer
m_commaSep   = Token.commaSep   m_lexer
m_lexeme     = Token.lexeme     m_lexer

-- Formula parser
expr :: Parser Formula
expr = buildExpressionParser table form

form = m_parens expr <|> literalTerm <|> quantifier <|> atom <?> "Error form"

literalTerm = (m_reserved "T" >> return (Val True) )
          <|> (m_reserved "F" >> return (Val False))
          <|> (m_reserved "⊤" >> return (Val True) )
          <|> (m_reserved "⊥" >> return (Val False))
          <?> "Error literalTerm"

quantifier = do { (m_lexeme . char) '@';  var <- m_identifier; (m_lexeme . char) '.'; form <- expr; return $ Forall var form } 
         <|> do { (m_lexeme . char) '\\'; var <- m_identifier; (m_lexeme . char) '.'; form <- expr; return $ Exists var form }
         <?> "Error quantifier"

atom = Atm <$> predicate <?> "Error atom"

-- Operator table, from highest to lowest priority
table = [ [ prefix "~" Not, prefix "¬" Not ]
        , [ binary "&" And AssocLeft, binary "∧" And AssocLeft ]
        , [ binary "|" Or  AssocLeft, binary "∨" Or  AssocLeft ]
        , [ binary "=>" Imp AssocLeft, binary "⇒" Imp AssocLeft ]
        , [ binary "==" Iff AssocLeft, binary "⇔" Iff AssocLeft ]
        ]

binary  name fun = Infix   (m_reservedOp name >> return fun)
prefix  name fun = Prefix  (m_reservedOp name >> return fun)
postfix name fun = Postfix (m_reservedOp name >> return fun)



-- Predicate parser
predicate :: Parser Pred
predicate = (do
    ident <- m_identifier
    terms <- m_parens (m_commaSep term)
    return $ Pred ident terms
    ) <?> "Error predicate"



-- Term parser
term :: Parser Term
term = try function
   <|> variable
   <?> "Error term"

variable = Var <$> m_identifier <?> "Error variable"

function = (do
    ident <- m_identifier
    terms <- m_parens (m_commaSep term)
    return $ Func ident terms
    ) <?> "Error function"

-- Parser
parseExp :: String -> Either ParseError Formula
parseExp = parse expr ""
