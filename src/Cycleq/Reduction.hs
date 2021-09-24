{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : Cycleq.Reduction
-- This module defines variable environments and the reduction of core expression.
module Cycleq.Reduction
  ( -- * Reduction Environment
    ReductionEnv (..),
    mkReductionEnv,

    -- * Reduction
    Reduct (..),
    reduce,
  )
where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer
import GHC.Data.Maybe
import GHC.Plugins hiding (empty)

-- * Reduction Environment

-- | The variable environment for reduction.
data ReductionEnv = ReductionEnv
  { reductionFreeVars :: IdSet,
    reductionBoundVars :: IdEnv CoreExpr,
    reductionInScopeSet :: InScopeSet
  }

-- | Make a program environment from a program.
mkReductionEnv :: [Id] -> CoreProgram -> ReductionEnv
mkReductionEnv xs binds =
  ReductionEnv
    { reductionFreeVars = mkVarSet xs,
      reductionBoundVars = mkVarEnv (flattenBinds binds),
      reductionInScopeSet = mkInScopeSet (mkVarSet (xs ++ bindersOfBinds binds))
    }

-- | Extend an environment with a local binder.
bindReductionEnv :: CoreBind -> ReductionEnv -> ReductionEnv
bindReductionEnv bind env =
  env
    { reductionBoundVars = extendVarEnvList (reductionBoundVars env) (flattenBinds [bind]),
      reductionInScopeSet = extendInScopeSetList (reductionInScopeSet env) (bindersOf bind)
    }

-- * Reduction

-- | A reduced core expression.
data Reduct = Reduct
  { reductExpr :: CoreExpr,
    reductIsProper :: Bool,
    reductStuckOn :: Maybe Id
  }

-- | Reduce a core expression as far as possible.
reduce :: forall m. MonadReader ReductionEnv m => CoreExpr -> m Reduct
reduce expr = handler (go False expr [])
  where
    handler :: MaybeT (WriterT (First Id) m) CoreExpr -> m Reduct
    handler m = do
      (expr', First x) <- runWriterT (runMaybeT m)
      pure
        Reduct
          { reductExpr = fromMaybe expr expr',
            reductIsProper = isJust expr',
            reductStuckOn = x
          }

    -- Reduce a core expression under a series of arguments.
    -- Non-proper reducts are permited if @notProper@ is set.
    go :: Bool -> CoreExpr -> [CoreArg] -> MaybeT (WriterT (First Id) m) CoreExpr
    go notProper (Var x) args = do
      ReductionEnv
        { reductionFreeVars = fvs,
          reductionBoundVars = bvs
        } <-
        ask
      case lookupVarEnv bvs x of
        Nothing
          | isDataConWorkId x -> do
            guard notProper
            pure (mkApps (Var x) args)
          | elemVarSet x fvs -> do
            guard notProper
            tell (First (Just x)) -- Mark x as preventing reduction
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
      scope <- asks reductionInScopeSet
      let subst = mkOpenSubst scope [(x, arg)]
      go True (substExpr subst body) args
    go notProper (Let bind body) [] =
      Let bind <$> local (bindReductionEnv bind) (go notProper body [])
    go notProper (Case scrut x ty alts) [] = do
      scrut' <- go True scrut []
      case viewNormalForm scrut' of
        Just (Left (con, args))
          | Just (_, patVars, rhs) <- findAlt (DataAlt con) alts -> do
            scope <- asks reductionInScopeSet
            let subst = mkOpenSubst scope ((x, scrut') : zip patVars args)
            go True (substExpr subst rhs) []
          | otherwise -> pprPanic "Incomplete case expression!" (ppr alts)
        Just (Right lit)
          | Just (_, [], rhs) <- findAlt (LitAlt lit) alts -> do
            go True rhs []
          | otherwise -> pprPanic "Incomplete case expression!" (ppr alts)
        Nothing -> empty
    go notProper expr' args =
      pprPanic "Unsupproted expression!" (ppr (mkApps expr' args))

-- | Match a core expression against a first-order normal form.
viewNormalForm :: CoreExpr -> Maybe (Either (DataCon, [CoreArg]) Literal)
viewNormalForm = go [] []
  where
    go :: [CoreBind] -> [CoreArg] -> CoreExpr -> Maybe (Either (DataCon, [CoreArg]) Literal)
    go binds args (Var x) =
      case isDataConWorkId_maybe x of
        Just con -> Just $ Left (con, fmap (\arg -> foldr Let arg binds) args)
        Nothing -> Nothing
    go binds args (Lit lit) = Just $ Right lit
    go binds args (App fun arg)
      | isValArg arg = go binds (arg : args) fun
      | otherwise = go binds args fun
    go binds [] (Let bind body) = go (bind : binds) [] body
    go _ _ _ = Nothing
