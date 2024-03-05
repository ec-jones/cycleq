module CycleQ.Syntax.Clause
  ( -- * Equations
    Equation (..),
    mkEquation,
    substEquation,

    -- * Hypotheses
    Hypotheses,
    applyHypotheses,

    -- * Clauses
    Clause (..),
    mkClause,
    clauseCriticals,
  )
where

import CycleQ.Syntax.Expr
import CycleQ.Syntax.Type
import Data.List qualified as List
import Data.Set qualified as Set

-- * Equations

-- | An atomic equation between expressions of the same type.
data Equation = Equation
  { -- | Critical equations in a clause.
    equationCriticals :: Set.Set Expr,
    equationLhs :: Expr,
    equationRhs :: Expr
  }

instance Show Equation where
  showsPrec _ (Equation _ lhs rhs) =
    shows lhs . showString " = " . shows rhs

-- | Make an equation with no critical information.
mkEquation :: Expr -> Expr -> Equation
mkEquation = Equation Set.empty

-- | Apply a substitution to an equation.
-- N.B. This function remove critical equations.
substEquation :: TySubst -> Subst -> Equation -> Equation
substEquation tyTheta theta (Equation criticals lhs rhs) =
  mkEquation (substExpr tyTheta theta lhs) (substExpr tyTheta theta rhs)

-- * Hypotheses

-- | A collection of hypotheses.
-- Equations must be irreducible, oriented, and have stable left-hand sides.
type Hypotheses = [Equation] -- Map.Map Expr Equation

-- | Apply any rewrite rule from the set of hypotheses.
applyHypotheses :: Hypotheses -> Expr -> (Bool, Expr)
applyHypotheses hyps expr =
  case List.find (\hyp -> equationLhs hyp == expr) hyps of
    Nothing
      | App fun arg <- expr ->
          let (p, fun') = applyHypotheses hyps fun
              (q, arg') = applyHypotheses hyps arg
           in (p || q, App fun' arg')
      | otherwise -> (False, expr)
    Just (Equation _ _ rhs) -> (True, rhs)

-- * Clauses

-- | An equational Horn clause.
data Clause = Clause
  { -- | Universally quantified variables.
    clauseVars :: [Var],
    -- | Universally quantified type variables.
    clauseTyVars :: [TyVar],
    -- | Orientated hypotheses.
    clauseHypRules :: Hypotheses,
    -- | Unorientated hypotheses.
    clauseHypEqs :: [Equation],
    -- | Consequent.
    clauseGoal :: Maybe Equation
  }

instance Show Clause where
  showsPrec _ clause =
    go
      ( clauseHypEqs clause
          ++ clauseHypRules clause
      )
    where
      go :: [Equation] -> ShowS
      go [] =
        case clauseGoal clause of
          Nothing -> id
          Just goal -> shows goal
      go [eq] = shows eq . showString " => " . go []
      go (eq : eqs) =
        shows eq . showString " /\\ " . go eqs

-- | Make a clause.
mkClause :: [TyVar] -> [Var] -> [Equation] -> Maybe Equation -> Clause
mkClause as xs hyps goal =
  Clause
    { clauseTyVars = as,
      clauseVars = xs,
      clauseHypEqs = hyps,
      clauseHypRules = [],
      clauseGoal = goal
    }

-- | Critical expressions in a clause.
clauseCriticals :: Clause -> Set.Set Expr
clauseCriticals Clause {clauseHypEqs = eqs, clauseHypRules = rules, clauseGoal = goal} =
  foldMap equationCriticals eqs
    <> foldMap equationCriticals rules
    <> foldMap equationCriticals goal
