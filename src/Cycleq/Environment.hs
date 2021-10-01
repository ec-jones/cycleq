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

    -- * Non-deterministic CoreM
    NonDetCoreM,
    runNonDetCoreM,
    firstSuccess,
  )
where

import Control.Monad.Logic
import Control.Applicative
import Control.Monad
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

type NonDetCoreM = LogicT CoreM

runNonDetCoreM :: NonDetCoreM a -> CoreM [a]
runNonDetCoreM = observeAllT

firstSuccess :: [NonDetCoreM a] -> NonDetCoreM a
firstSuccess [] = empty
firstSuccess (m : ms) =
  msplit m >>= \case
    Nothing -> firstSuccess ms
    Just (res, alts) -> pure res <|> alts

-- -- | The main monad that enhances @CoreM@ with non-determinism.
-- -- Although CoreM is not-commutative, it is only used as a unique supply which is commutative /up-to/ renaming.
-- newtype NonDetCoreM a = NonDetCoreM
--   { runNonDetCoreM :: CoreM [a]
--   }
--   deriving
--     (Functor, Applicative, Alternative)
--     via (WrappedMonad NonDetCoreM)

-- instance Monad NonDetCoreM where
--   return = NonDetCoreM . pure . pure

--   NonDetCoreM m >>= f =
--     NonDetCoreM (m >>= (fmap concat . mapM (runNonDetCoreM . f)))

-- instance MonadPlus NonDetCoreM where
--   mzero = NonDetCoreM (pure [])

--   mplus (NonDetCoreM m1) (NonDetCoreM m2) =
--     NonDetCoreM (liftA2 (++) m1 m2)

-- instance MonadUnique NonDetCoreM where
--   getUniqueSupplyM =
--     NonDetCoreM (pure <$> getUniqueSupplyM)

-- -- | Select the first branch that produces any result.
-- firstSuccess :: [NonDetCoreM a] -> NonDetCoreM a
-- firstSuccess [] = empty
-- firstSuccess (m : ms) =
--   NonDetCoreM $
--     runNonDetCoreM m >>= \case
--       [] -> runNonDetCoreM (firstSuccess ms)
--       res -> pure res
