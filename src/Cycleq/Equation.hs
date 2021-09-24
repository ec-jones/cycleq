-- |
-- Module      : Cycleq.Equation
-- This module defines equations and some basic functions for their manipulation.
module Cycleq.Equation
  ( -- * Equations
    Equation (..),
    fromCore,
    subtermsForSuper,
  )
where

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
      char '∀' <+> interpp'SP xs GHC.Plugins.<> dot <+> body
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
fromCore :: CoreExpr -> Maybe Equation
fromCore expr
  | let (xs, body) = collectBinders expr,
    (Var eq, [ty, lhs, rhs]) <- collectArgs body,
    occName eq == mkVarOcc "≃" =
    Just (Equation (filter isId xs) lhs rhs)
  | otherwise = Nothing

-- | The non-variable subterms of an equation.
subtermsForSuper :: Equation -> [(CoreExpr, CoreExpr -> Equation)]
subtermsForSuper (Equation xs lhs rhs) = lefts ++ rights
  where
    lefts, rights :: [(CoreExpr, CoreExpr -> Equation)]
    lefts =
      second (flip (Equation xs) rhs .) <$> exprSubtermsForSuper lhs
    rights =
      second (Equation xs lhs .) <$> exprSubtermsForSuper rhs

-- | The non-variable subterms of an expression.
exprSubtermsForSuper :: CoreExpr -> [(CoreExpr, CoreExpr -> CoreExpr)]
exprSubtermsForSuper (App fun arg) =
  (App fun arg, id) :
  (second (App fun .) <$> exprSubtermsForSuper arg)
    ++ (second (flip App arg .) <$> exprSubtermsForSuper fun)
exprSubtermsForSuper (Lam x body) =
  (Lam x body, id) :
  (second (Lam x .) <$> exprSubtermsForSuper body)
exprSubtermsForSuper (Let bind body) =
  (Let bind body, id) :
  (second (Let bind .) <$> exprSubtermsForSuper body)
exprSubtermsForSuper _ = []
