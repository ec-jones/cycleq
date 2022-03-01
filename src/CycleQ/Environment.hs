-- |
-- Module: Cycleq.Environment
module CycleQ.Environment
  ( ProgramEnv,
    mkProgramEnv,
    EquationEnv (..),
    intoEquationEnv,
    extendBoundVars,
    extendFreeVars,
  )
where

import GHC.Plugins hiding (empty)

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
extendBoundVars :: CoreBind -> EquationEnv -> EquationEnv
extendBoundVars bind env =
  env
    { envBoundVars = extendVarEnvList (envBoundVars env) (flattenBinds [bind]),
      envInScopeSet = extendInScopeSetList (envInScopeSet env) (bindersOf bind)
    }

-- | Extend an equation environment with a free variable.
extendFreeVars :: Id -> EquationEnv -> EquationEnv
extendFreeVars x env =
  env
    { envFreeVars = extendVarSet (envFreeVars env) x,
      envInScopeSet = extendInScopeSet (envInScopeSet env) x
    }

-- | Extend the prover environment with the free variables of an equation.
intoEquationEnv :: [Id] -> ProgramEnv -> EquationEnv
intoEquationEnv xs prog =
  EquationEnv
    { envFreeVars = mkVarSet xs,
      envBoundVars = progBoundVars prog,
      envInScopeSet = extendInScopeSetList (progInScopeSet prog) xs
    }
