{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}

-- |
-- Module: Cycleq.Environment
module Cycleq.Environment
  ( -- * Variable Environment
    ProgramEnv,
    mkProgramEnv,
    EquationEnv (envFreeVars, envBoundVars, envInScopeSet),
    intoEquationEnv,
    extendEquationEnv,

    -- * Non-deterministic CoreM
    NonDetCoreM,
    runNonDetCoreM,
    firstSuccess,
  )
where

import Control.Monad
import Control.Applicative
import qualified Data.DList as DList
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

-- * Non-deterministic CoreM

-- | The main monad that enhances @CoreM@ with non-determinism.
newtype NonDetCoreM a = NonDetCoreM
  { -- | Although CoreM is not-commutative, it is only used as a unique supply which is commutative /up-to/ renaming.
    _runNonDetCoreM :: CoreM (DList.DList a)
  }
  deriving
    (Functor, Applicative, Alternative)
    via (WrappedMonad NonDetCoreM)

instance Monad NonDetCoreM where
  return = NonDetCoreM . pure . DList.singleton

  NonDetCoreM m >>= f =
    NonDetCoreM (m >>= (fmap (DList.foldr DList.append DList.empty) . mapM (_runNonDetCoreM . f)))

instance MonadPlus NonDetCoreM where
  mzero = NonDetCoreM (pure DList.empty)

  mplus (NonDetCoreM m1) (NonDetCoreM m2) =
    NonDetCoreM (liftA2 DList.append m1 m2)

instance MonadUnique NonDetCoreM where
  getUniqueSupplyM =
    NonDetCoreM (DList.singleton <$> getUniqueSupplyM)

-- | Run a non-deterministic action to produce a list of possible results.
runNonDetCoreM :: NonDetCoreM a -> CoreM [a]
runNonDetCoreM = fmap DList.toList . _runNonDetCoreM 

-- | Select the first branch that produces any result.
firstSuccess :: [NonDetCoreM a] -> NonDetCoreM a
firstSuccess [] = empty
firstSuccess (m : ms) = NonDetCoreM $
  _runNonDetCoreM m >>= \case
    DList.Nil -> _runNonDetCoreM (firstSuccess ms)
    res -> pure res
