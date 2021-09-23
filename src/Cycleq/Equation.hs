-- |
-- Module      : Cycleq.Equation
-- This module defines equations and some basic functions for their manipulation.
module Cycleq.Equation
  ( -- * Equations
    Equation (..),
    fromCore,
    substEquation,
    equationSubtermsForSuper,
  )
where

import Cycleq.Patterns
import Data.Bifunctor
import GHC.Plugins hiding (empty)

-- | Simple equation between core expressions
data Equation = Equation
  { -- | Universally quantified variables
    equationVars :: [Id],
    -- | Left-hand side of the equation
    equationLeft :: CoreExpr,
    -- | Right-hand side of the equation
    equationRight :: CoreExpr
  }

instance Outputable Equation where
  ppr (Equation xs lhs rhs)
    | not (null xs) =
      forAllLit <+> interpp'SP xs GHC.Plugins.<> dot <+> body
    | otherwise = body
    where
      body :: SDoc
      body =
        -- Suppress type applications
        updSDocContext (\sdoc -> sdoc {sdocSuppressTypeApplications = True}) $
          -- Never qualify names
          withPprStyle (mkUserStyle neverQualify (PartWay 0)) $
            ppr lhs <+> char '≃' <+> ppr rhs

-- | Interpret a core expression as an equation
fromCore :: CoreExpr -> Equation
fromCore (Lams xs (Apps (Var eq) [ty, lhs, rhs]))
  | occName eq == mkVarOcc "≃" = Equation xs lhs rhs
fromCore expr = pprPanic "Couldn't parse equation!" (ppr expr)

-- | Apply a substitution to both sides of an equation.
substEquation :: Subst -> Equation -> Equation
substEquation subst (Equation xs lhs rhs) =
  Equation xs (substExpr subst lhs) (substExpr subst rhs)

-- | Choose a subterm of an equation that is suitable for superposition.
equationSubtermsForSuper :: Equation -> [(CoreExpr, CoreExpr -> Equation)]
equationSubtermsForSuper (Equation xs lhs rhs) = lefts ++ rights
  where
    lefts, rights :: [(CoreExpr, CoreExpr -> Equation)]
    lefts =
      second (flip (Equation xs) rhs .) <$> subtermsForSuper lhs
    rights =
      second (Equation xs lhs .) <$> subtermsForSuper rhs

-- | Choose a subterm that is suitable for superposition.
subtermsForSuper :: CoreExpr -> [(CoreExpr, CoreExpr -> CoreExpr)]
subtermsForSuper (App fun arg) =
  (App fun arg, id) :
  (second (App fun .) <$> subtermsForSuper arg)
    ++ (second (flip App arg .) <$> subtermsForSuper fun)
subtermsForSuper (Lam x body) =
  (Lam x body, id) :
  (second (Lam x .) <$> subtermsForSuper body)
subtermsForSuper (Let bind body) =
  (Let bind body, id) :
  (second (Let bind .) <$> subtermsForSuper body)
subtermsForSuper _ = []
