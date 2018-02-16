module AST where

data Formula = Val Bool             -- Constant True/False
             | Atm Pred             -- Predicate
             | Not Formula          -- Negation
             | And Formula Formula  -- Conjunction
             | Or  Formula Formula  -- Disjunction
             | Imp Formula Formula  -- Implication
             | Iff Formula Formula  -- Equivalence
             | Forall String Formula  -- Universal quantifier
             | Exists String Formula  -- Existential quantifier
    deriving(Eq, Ord, Show)

data Pred = Pred String [Term]  -- Predicate
    deriving(Eq, Ord, Show)

data Term = Var String          -- Variable
          | Func String [Term]  -- Function
    deriving(Eq, Ord, Show)
