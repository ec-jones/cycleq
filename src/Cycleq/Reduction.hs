{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module: Cycleq.Reduction
module Cycleq.Reduction
  ( -- * Reduction
    ReductT,
    runReductT,
    reduce,
    viewNormalForm,
  )
where

import Control.Applicative
import Control.Monad.Reader
import Cycleq.Environment
import GHC.Plugins hiding (empty)

-- * Reduction

-- | Reduce a core expression as far as possible.
reduce :: forall m. (MonadUnique m, MonadReader EquationEnv m) => CoreExpr -> ReductT m CoreExpr
reduce expr = go expr []
  where
    -- Reduce a core expression under a series of arguments.
    go :: CoreExpr -> [CoreArg] -> ReductT m CoreExpr
    go (Var x) args = do
      env <- ask
      case lookupVarEnv (envBoundVars env) x of
        Nothing
          | isDataConWorkId x ->
            pure (mkApps (Var x) args)
          | elemVarSet x (envFreeVars env) -> do
            stuckOn x
            pure (mkApps (Var x) args)
          | otherwise -> pprPanic "Variable not in scope!" (ppr x)
        Just defn ->
          ( do
              isProper
              go defn args
          )
            <|> pure (mkApps (Var x) args)
    go (Lit lit) args = pure (mkApps (Lit lit) args)
    go (App fun arg) args = do
      -- Full-beta stategy
      arg' <- notNeeded (go arg [])
      go fun (arg' : args)
    go (Lam x body) [] =
      -- Full-beta stategy
      Lam x <$> local (extendFreeVars x) (notNeeded $ go body [])
    go (Lam x body) (arg : args) = do
      isProper
      scope <- asks envInScopeSet
      let subst = mkOpenSubst scope [(x, arg)]
      go (substExpr subst body) args
    go (Let bind body) args = do
      (bind', subst) <- freshenBind bind
      body' <- local (extendBoundVars bind') $ go (substExpr subst body) args
      pure (Let bind' body')
    go (Case scrut x ty alts) args = do
      scrut' <- go scrut []
      case viewNormalForm scrut' of
        Just (Left (con, conArgs))
          | Just (_, patVars, rhs) <- findAlt (DataAlt con) alts -> do
            isProper
            scope <- asks envInScopeSet
            let subst = mkOpenSubst scope ((x, scrut') : zip patVars conArgs)
            go (substExpr subst rhs) args
          | otherwise -> pprPanic "Incomplete case expression!" (ppr alts)
        Just (Right lit)
          | Just (_, [], rhs) <- findAlt (LitAlt lit) alts -> do
            isProper
            go rhs args
          | otherwise -> pprPanic "Incomplete case expression!" (ppr alts)
        Nothing -> empty
    go (Type ty) args = pure (mkApps (Type ty) args)
    go expr' args =
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

-- * Reduction Monad

-- | The reduction monad records if progress has been made
-- and which variable prevents further progress.
newtype ReductT m a = ReductT
  { unReductT :: m (Maybe (a, Bool), Maybe Id)
  }

instance Monad m => Functor (ReductT m) where
  fmap f m = ReductT $ do
    (res, x) <- unReductT m
    case res of
      Nothing -> pure (Nothing, x)
      Just (a, p) -> pure (Just (f a, p), x)

instance Monad m => Applicative (ReductT m) where
  pure x = ReductT $ pure (Just (x, False), Nothing)

  m1 <*> m2 = ReductT $ do
    (res1, x) <- unReductT m1
    (res2, y) <- unReductT m2
    case res1 of
      Nothing -> pure (Nothing, x <|> y)
      Just (f, p) ->
        case res2 of
          Nothing -> pure (Nothing, x <|> y)
          Just (a, q) -> pure (Just (f a, p || q), x <|> y)

instance Monad m => Alternative (ReductT m) where
  empty = ReductT $ pure (Nothing, Nothing)

  m1 <|> m2 = ReductT $ do
    (res1, x1) <- unReductT m1
    (res2, x2) <- unReductT m2
    pure (res1 <|> res2, x1 <|> x2)

instance Monad m => Monad (ReductT m) where
  return x = ReductT $ pure (Just (x, False), Nothing)

  m >>= f = ReductT $ do
    (res, x) <- unReductT m
    case res of
      Nothing -> pure (Nothing, x)
      Just (a, p) -> do
        (res', y) <- unReductT (f a)
        case res' of
          Nothing -> pure (Nothing, x <|> y)
          Just (b, q) -> pure (Just (b, p || q), x <|> y)

instance MonadReader env m => MonadReader env (ReductT m) where
  ask = ReductT $ do
    env <- ask
    pure (Just (env, False), Nothing)

  local f m = ReductT $ local f $ unReductT m

instance MonadUnique m => MonadUnique (ReductT m) where
  getUniqueSupplyM = ReductT $ do
    supply <- getUniqueSupplyM
    pure (Just (supply, False), Nothing)

-- | Evaluate a reduct action.
runReductT :: MonadPlus m => ReductT m a -> m (a, Bool, Maybe Id)
runReductT m = do
  (res, x) <- unReductT m
  case res of
    Nothing -> empty
    Just (a, p) -> pure (a, p, x)

-- | Mark a variable as preventing progress.
stuckOn :: Monad m => Id -> ReductT m ()
stuckOn x = ReductT $ pure (Just ((), False), Just x)

-- | Supress stuckOn.
notNeeded :: Monad m => ReductT m a -> ReductT m a
notNeeded m = ReductT $ do
  (res, x) <- unReductT m
  pure (res, Nothing)

-- | Mark a proper reduction step.
isProper :: Monad m => ReductT m ()
isProper = ReductT $ pure (Just ((), True), Nothing)

-- | Rename a core bind to prevent capture.
freshenBind :: (MonadUnique m) => CoreBind -> m (CoreBind, Subst)
freshenBind (NonRec x defn) = do
  x' <- freshenVar x
  let scope = mkInScopeSet (mkVarSet [x'])
      subst = mkOpenSubst scope [(x, Var x')]
  pure (NonRec x' defn, subst)
freshenBind (Rec binds) = do
  (xs, xs', defns) <-
    unzip3
      <$> mapM
        ( \(x, defn) -> do
            x' <- freshenVar x
            pure (x, x', defn)
        )
        binds
  let scope = mkInScopeSet (mkVarSet xs')
      subst = mkOpenSubst scope (zip xs (fmap Var xs'))
      defns' = fmap (substExpr subst) defns
  pure (Rec (zip xs' defns'), subst)

-- | Create a fresh variable of a given type.
freshenVar :: MonadUnique m => CoreBndr -> m Id
freshenVar x = setVarUnique x <$> getUniqueM
