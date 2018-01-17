module Logic.Parser(parseExpr) where

import Logic.AST
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token as Token
import Text.Parsec.Language
-- import qualified Text.Parsec.Lexer as L

-- Language definition
def = emptyDef { identStart = letter
               , identLetter = alphaNum
               , opStart = oneOf "&|>="
               , opLetter = oneOf "&|>="
               , reservedOpNames = ["&", "|", ">", "="]
               , reservedNames = ["T","F"]
               }

-- Lexer based on that definition
lexer = makeTokenParser def

-- Parsers

m_parens = Token.parens lexer
m_reserved = Token.reserved lexer
m_reservedOp = Token.reservedOp lexer
m_identifier = Token.identifier lexer

expr :: Parser Formula
expr = buildExpressionParser table term

term = m_parens expr <|> atomicTerm

atomicTerm = literalTerm <|> identifierTerm

literalTerm = (m_reserved "T" >> return (Val True))
          <|> (m_reserved "F" >> return (Val False))

identifierTerm = Var <$> m_identifier

-- Operator table, from biggest to lowest priority
table = [ [ prefix "-" Not ]
        , [ binary "&" And AssocLeft ]
        , [ binary "|" Or AssocLeft ]
        , [ binary ">" Imp AssocLeft ]
        , [ binary "=" Iff AssocLeft ]
        ]

binary  name fun assoc = Infix   (m_reservedOp name >> return fun ) assoc
prefix  name fun       = Prefix  (m_reservedOp name >> return fun )
postfix name fun       = Postfix (m_reservedOp name >> return fun )

-- Parser
parseExpr :: String -> Either ParseError Formula
parseExpr = parse expr ""
