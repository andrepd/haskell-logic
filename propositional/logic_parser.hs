module PropLogic.Parser(parseExp) where

import PropLogic.AST
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token as Token
import Text.Parsec.Language
-- import qualified Text.Parsec.Lexer as L

-- Language definition
def = emptyDef { identStart = letter
               , identLetter = alphaNum
               , opStart = oneOf "&|>=~∧∨⇒⇔"
               , opLetter = oneOf ""
               , reservedOpNames = ["&", "|", ">", "=", "~", "∧", "∨", "⇒", "⇔"]
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
          <|> (m_reserved "⊤" >> return (Val True))
          <|> (m_reserved "⊥" >> return (Val False))

identifierTerm = Var <$> m_identifier

-- Operator table, from highest to lowest priority
table = [ [ prefix "~" Not, prefix "¬" Not ]
        , [ binary "&" And AssocLeft, binary "∧" And AssocLeft ]
        , [ binary "|" Or  AssocLeft, binary "∨" Or  AssocLeft ]
        , [ binary ">" Imp AssocLeft, binary "⇒" Imp AssocLeft ]
        , [ binary "=" Iff AssocLeft, binary "⇔" Iff AssocLeft ]
        ]

binary  name fun assoc = Infix   (m_reservedOp name >> return fun ) assoc
prefix  name fun       = Prefix  (m_reservedOp name >> return fun )
postfix name fun       = Postfix (m_reservedOp name >> return fun )

-- Parser
parseExp :: String -> Either ParseError Formula
parseExp = parse expr ""
