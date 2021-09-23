{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module      : Cycleq.Reduction
-- This module defines variable environments and the reduction of core expression.
module Cycleq.Reduction
  ( -- * Reduction
    Reduct (..),
    reduce,

    -- * Variable Environments
    ProgramEnv (..),
    mkProgramEnv,
    EquationEnv (..),
    mkEquationEnv,
    extendEnvBind,

    -- * Pattern Utilities
    viewConApp,
    viewLit,
  )
where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer
import GHC.Data.Maybe
import GHC.Plugins hiding (empty)

-- * Reduction

-- | A reduced core expression.
data Reduct = Reduct
  { reductExpr :: CoreExpr,
    reductIsProper :: Bool,
    reductStuckOn :: Maybe Id
  }

-- | The reduction monad.
newtype ReduceT m a = ReduceT
  { unReduceT :: MaybeT (WriterT (First Id) m) a
  }
  deriving newtype
    (Functor, Applicative, Alternative, Monad, MonadPlus)

instance MonadReader r m => MonadReader r (ReduceT m) where
  ask = ReduceT ask
  local f (ReduceT m) = ReduceT (local f m)

-- | Extract a reduct from the reduction monad.
runReduceT :: Monad m => CoreExpr -> ReduceT m CoreExpr -> m Reduct
runReduceT expr m = do
  ( maybe (False, expr) (True,) -> (reductIsProper, reductExpr),
    getFirst -> reductStuckOn
    ) <-
    runWriterT $ runMaybeT $ unReduceT m
  pure Reduct {..}

-- | Mark a variable as preventing progress.
stuckOn :: Monad m => Id -> ReduceT m ()
stuckOn = ReduceT . tell . First . Just

-- | Reduce a core expression as far as possible.
reduce :: forall m. MonadReader EquationEnv m => CoreExpr -> m Reduct
reduce expr = runReduceT expr (go False expr [])
  where
    -- Reduce a core expression under a number of arguments.
    -- Non-proper reducts are permited if notProper is set.
    go ::
      Bool ->
      CoreExpr ->
      [CoreArg] ->
      ReduceT m CoreExpr
    go notProper (Var x) args = do
      EquationEnv {envBoundVars, envFreeVars} <- ask
      case lookupVarEnv envBoundVars x of
        Nothing
          | isDataConWorkId x-> do
            guard notProper
            pure (mkApps (Var x) args)
          | elemVarSet x envFreeVars -> do
            guard notProper
            stuckOn x
            pure (mkApps (Var x) args)
          | otherwise -> pprPanic "Variable not in scope!" (ppr x)
        Just defn ->
          go True defn args
            <|> ( do
                    guard notProper
                    pure (mkApps (Var x) args)
                )
    go notProper (Lit lit) args = pure (mkApps (Lit lit) args)
    go notProper (App fun arg) args = go notProper fun (arg : args)
    go notProper (Lam x body) [] = empty
    go notProper (Lam x body) (arg : args) = do
      EquationEnv {envInScopeSet} <- ask
      let subst = mkOpenSubst envInScopeSet [(x, arg)]
      go True (substExpr subst body) args
    go notProper (Let bind body) [] =
      Let bind <$> local (extendEnvBind bind) (go notProper body [])
    go notProper (Case scrut x ty alts) [] = do
      EquationEnv {envInScopeSet} <- ask
      scrut' <- go True scrut []
      case scrut' of
        (viewConApp -> Just (con, args))
          | Just (_, patVars, rhs) <- findAlt (DataAlt con) alts -> do
            let subst = mkOpenSubst envInScopeSet ((x, scrut') : zip patVars args)
            go True (substExpr subst rhs) []
        (viewLit -> Just lit)
          | Just (_, [], rhs) <- findAlt (LitAlt lit) alts -> do
            go True rhs []
        nonCon -> empty
    go notProper expr args =
      pprPanic "Unexpected unsupproted expression!" (ppr (mkApps expr args))

-- * Variable Environments

-- | A program level variable environment.
data ProgramEnv = ProgramEnv
  { envBoundVars :: IdEnv CoreExpr,
    envInScopeSet :: InScopeSet
  }

-- | Make a program environment from a program.
mkProgramEnv :: CoreProgram -> ProgramEnv
mkProgramEnv binds =
  let envBoundVars = mkVarEnv (flattenBinds binds)
      envInScopeSet = mkInScopeSet (mkVarSet (bindersOfBinds binds))
   in ProgramEnv {..}

-- | A local level variable environment.
data EquationEnv = EquationEnv
  { envFreeVars :: IdSet,
    envBoundVars :: IdEnv CoreExpr,
    envInScopeSet :: InScopeSet
  }

-- | Add local free variables to a program environment.
mkEquationEnv :: [Id] -> ProgramEnv -> EquationEnv
mkEquationEnv xs ProgramEnv {envBoundVars, envInScopeSet = progScope} =
  let envFreeVars = mkVarSet xs
      envInScopeSet = extendInScopeSetList progScope xs
   in EquationEnv {..}

-- | Extend a environment with a local binder.
extendEnvBind :: CoreBind -> EquationEnv -> EquationEnv
extendEnvBind bind ctx@EquationEnv {envBoundVars, envInScopeSet} =
  ctx
    { envBoundVars = extendVarEnvList envBoundVars (flattenBinds [bind]),
      envInScopeSet = extendInScopeSetList envInScopeSet (bindersOf bind)
    }

-- * Pattern Utilities

-- | Core expressions that are the application of a data constructor to several arguments.
viewConApp :: CoreExpr -> Maybe (DataCon, [CoreArg])
viewConApp = go [] []
  where
    go binds args (Var x) = do
      con <- isDataConWorkId_maybe x
      pure (con, fmap (\arg -> foldr Let arg binds) args)
    go binds args (App fun arg)
      | isValArg arg = go binds (arg : args) fun
      | otherwise = go binds args fun
    go binds [] (Let bind body) = go (bind : binds) [] body
    go _ _ _ = Nothing

-- | Core expressions that are literals under a number of let-bindings.
viewLit :: CoreExpr -> Maybe Literal
viewLit (Lit lit) = Just lit
viewLit (Let _ body) = viewLit body
viewLit _ = Nothing