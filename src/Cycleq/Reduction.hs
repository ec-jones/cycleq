{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : Cycleq.Reduction
module Cycleq.Reduction
  ( -- * Reduction
    Reduct (..),
    reduce,
    viewNormalForm,
  )
where

import Control.Monad.Writer
import Control.Monad.Reader
import Cycleq.Environment
import GHC.Data.Maybe
import Control.Applicative
import GHC.Plugins hiding (empty)

-- * Reduction

-- | A reduced core expression.
data Reduct = Reduct
  { reductExpr :: CoreExpr,
    reductIsProper :: Bool,
    reductStuckOn :: Maybe Id
  }

-- | Reduce a core expression as far as possible.
reduce :: forall m. MonadReader EquationEnv m => CoreExpr -> m Reduct
reduce expr = handler (go False expr [])
  where
    -- Produce a 'Reduct' from an effectful expression.
    -- Failure is interpreted as a non-proper reduction
    -- The Writer records which variable is preventing further reduction.
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
      env <- ask
      case lookupVarEnv (envBoundVars env) x of
        Nothing
          | isDataConWorkId x -> do
            guard notProper
            pure (mkApps (Var x) args)
          | elemVarSet x (envFreeVars env) -> do
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
      scope <- asks envInScopeSet
      let subst = mkOpenSubst scope [(x, arg)]
      go True (substExpr subst body) args
    go notProper (Let bind body) [] =
      Let bind <$> local (extendEquationEnv bind) (go notProper body [])
    go notProper (Case scrut x ty alts) args = do
      scrut' <- go True scrut []
      case viewNormalForm scrut' of
        Just (Left (con, conArgs))
          | Just (_, patVars, rhs) <- findAlt (DataAlt con) alts -> do
            scope <- asks envInScopeSet
            let subst = mkOpenSubst scope ((x, scrut') : zip patVars conArgs)
            go True (substExpr subst rhs) args
          | otherwise -> pprPanic "Incomplete case expression!" (ppr alts)
        Just (Right lit)
          | Just (_, [], rhs) <- findAlt (LitAlt lit) alts -> do
            go True rhs args
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
