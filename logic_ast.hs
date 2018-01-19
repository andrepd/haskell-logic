module Logic.AST where

data Formula = Val Bool             -- Constant True/False
             | Var String           -- Atom
             | Not Formula          -- Negation
             | And Formula Formula  -- Conjunction
             | Or  Formula Formula  -- Disjunction
             | Imp Formula Formula  -- Implication
             | Iff Formula Formula  -- Equivalence
    deriving(Eq, Ord)
