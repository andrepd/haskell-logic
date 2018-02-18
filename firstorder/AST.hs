module AST where

data Formula = Val Bool                -- Constant True/False
             | Pred String [Term]  -- Predicate
             | Not Formula             -- Negation
             | And Formula Formula     -- Conjunction
             | Or  Formula Formula     -- Disjunction
             | Imp Formula Formula     -- Implication
             | Iff Formula Formula     -- Equivalence
             | Forall String Formula   -- Universal quantifier
             | Exists String Formula   -- Existential quantifier
    deriving(Eq, Ord, Show)

data Term = Var String          -- Variable
          | Func String [Term]  -- Function
    deriving(Eq, Ord, Show)
