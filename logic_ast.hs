module Logic.AST where

data Formula = Val Bool
             | Var String
             | Not Formula
             | And Formula Formula
             | Or  Formula Formula
             | Imp Formula Formula
             | Iff Formula Formula
    deriving(Show)