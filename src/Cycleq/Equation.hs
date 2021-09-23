{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

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

import Control.Applicative
import Data.Foldable
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
  ppr Equation {equationVars, equationLeft, equationRight}
#ifdef DEBUG
    | not (null equationVars) =
      forAllLit <+> interpp'SP equationVars GHC.Plugins.<> dot <+> body
#endif
    | otherwise = body
    where
      body :: SDoc
      body =
        -- Suppress type applications
        updSDocContext (\sdoc -> sdoc {sdocSuppressTypeApplications = True}) $
          -- Never qualify names
          withPprStyle (mkUserStyle neverQualify (PartWay 0)) $
            ppr equationLeft <+> char '≃' <+> ppr equationRight

-- | Interpret a core expression as an equation
fromCore :: CoreExpr -> Equation
fromCore srcExpr
  | let (binders, body) = collectBinders srcExpr
        equationVars = filter isId binders,
    (Var eq, [ty, equationLeft, equationRight]) <- collectArgs body,
    occName eq == mkVarOcc "≃" =
    Equation {..}
  | otherwise = pprPanic "Couldn't interpret core expression as equation!" (ppr srcExpr)

-- | Apply a substitution to both sides of an equation
substEquation :: Subst -> Equation -> Equation
substEquation subst eq@Equation {equationLeft, equationRight} =
  eq
    { equationLeft = substExpr subst equationLeft,
      equationRight = substExpr subst equationRight
    }

-- | Choose a subterm of an equation that is suitable for superposition
equationSubtermsForSuper :: Equation -> [(CoreExpr, CoreExpr -> Equation)]
equationSubtermsForSuper eq@Equation {equationLeft, equationRight} =
  ( do
      ~(expr, k) <- subtermsForSuper equationLeft
      pure (expr, \expr' -> eq {equationLeft = k expr'})
  )
    <|> ( do
            ~(expr, k) <- subtermsForSuper equationRight
            pure (expr, \expr' -> eq {equationRight = k expr'})
        )

-- | Choose a subterm that is suitable for superposition
subtermsForSuper :: CoreExpr -> [(CoreExpr, CoreExpr -> CoreExpr)]
subtermsForSuper (App fun arg) =
  asum
    [ pure (App fun arg, id),
      do
        ~(expr, k) <- subtermsForSuper fun
        pure (expr, flip App arg . k),
      do
        ~(expr, k) <- subtermsForSuper arg
        pure (expr, App fun . k)
    ]
subtermsForSuper (Lam x body) =
  asum
    [ pure (Lam x body, id),
      do
        ~(expr, k) <- subtermsForSuper body
        pure (expr, Lam x . k)
    ]
subtermsForSuper (Let bind body) =
  asum
    [ pure (Let bind body, id),
      do
        ~(expr, k) <- subtermsForSuper body
        pure (expr, Let bind . k)
    ]
subtermsForSuper _ = empty
