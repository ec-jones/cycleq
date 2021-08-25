{-# LANGUAGE ImplicitParams #-}

module Unconditional where

import Control.Applicative
import GHC.Plugins hiding (empty)
import Syntax

data Context = Context
  { boundVars :: VarEnv CoreExpr,
    inScopeSet :: InScopeSet
  }

simplify :: (?ctx :: Context, Alternative m) => Equation -> m [Equation]
simplify (Equation lhs rhs)
  -- Reflexivity
  | eqExpr (inScopeSet ?ctx) lhs rhs = pure []
  -- Congruence
  | (Var con, conArgs) <- collectArgs lhs,
    (Var con', conArgs') <- collectArgs rhs,
    isDataConWorkId con,
    isDataConWorkId con' = do
    guard (con == con')
    pure (zipWith Equation conArgs conArgs')
  -- Narrowing
  | otherwise = do
    lhs' <- normalise lhs
    rhs' <- normalise rhs
    pure [Equation rhs' lhs']