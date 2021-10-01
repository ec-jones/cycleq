{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module: Cycleq.Environment
module Cycleq.Environment
  ( -- * Variable Environment
    ProgramEnv,
    mkProgramEnv,
    EquationEnv (envFreeVars, envBoundVars, envInScopeSet),
    intoEquationEnv,
    extendEquationEnv,
  )
where

import GHC.Plugins hiding (empty)

-- * Variable Environments

-- | Program level variable environment.
data ProgramEnv = ProgramEnv
  { progBoundVars :: IdEnv CoreExpr,
    progInScopeSet :: InScopeSet
  }

-- | Make a program level variable environment from a program.
mkProgramEnv :: CoreProgram -> ProgramEnv
mkProgramEnv binds =
  ProgramEnv
    { progBoundVars = mkVarEnv (flattenBinds binds),
      progInScopeSet = mkInScopeSet (mkVarSet (bindersOfBinds binds))
    }

-- | Equation level variable environment.
data EquationEnv = EquationEnv
  { envFreeVars :: IdSet,
    envBoundVars :: IdEnv CoreExpr,
    envInScopeSet :: InScopeSet
  }

-- | Extend an equation environment with a local bind.
extendEquationEnv :: CoreBind -> EquationEnv -> EquationEnv
extendEquationEnv bind env =
  env
    { envBoundVars = extendVarEnvList (envBoundVars env) (flattenBinds [bind]),
      envInScopeSet = extendInScopeSetList (envInScopeSet env) (bindersOf bind)
    }

-- | Extend the prover environment with the free variables of an equation.
intoEquationEnv :: [Id] -> ProgramEnv -> EquationEnv
intoEquationEnv xs prog =
  EquationEnv
    { envFreeVars = mkVarSet xs,
      envBoundVars = progBoundVars prog,
      envInScopeSet = extendInScopeSetList (progInScopeSet prog) xs
    }