{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Cycleq.Reduction where

import Control.Applicative
import Control.Monad.Freer
import Control.Monad.Freer.NonDet
import Control.Monad.Freer.Reader
import Control.Monad.Freer.State
import GHC.Plugins hiding (empty)

-- * Reduction Context

-- | A reduction context.
data Context = Context
  { contextFreeVars :: IdSet,
    contextBoundVars :: IdEnv CoreExpr,
    contextInScopeSet :: InScopeSet
  }

-- | Make a context from a program and list of free variables.
mkContext :: [CoreBind] -> Context
mkContext binds =
  Context
    { contextFreeVars = emptyVarSet,
      contextBoundVars = mkVarEnv (flattenBinds binds),
      contextInScopeSet = mkInScopeSet (mkVarSet (bindersOfBinds binds))
    }

-- | Extend a context with a binder.
extendContextBind :: CoreBind -> Context -> Context
extendContextBind bind ctx@Context {contextBoundVars, contextInScopeSet} =
  ctx
    { contextBoundVars = extendVarEnvList contextBoundVars (flattenBinds [bind]),
      contextInScopeSet = extendInScopeSetList contextInScopeSet (bindersOf bind)
    }

-- | Extend a context with free variables.
extendContextFreeVars :: [Id] -> Context -> Context
extendContextFreeVars xs ctx@Context {contextFreeVars, contextInScopeSet} =
  ctx
    { contextFreeVars = extendVarSetList contextFreeVars xs,
      contextInScopeSet = extendInScopeSetList contextInScopeSet xs
    }

-- * Reduction

-- | A reduced core expression
data Reduct = Reduct
  { reductExpr :: CoreExpr,
    reductIsProper :: Bool,
    reductStuck :: Maybe Id
  }

-- | Make a 'Reduct' from the final state of reduction.
mkReduct :: CoreExpr -> (Maybe (CoreExpr, Bool), Maybe Id) -> Reduct
mkReduct expr (Nothing, stuck) =
  Reduct
    { reductExpr = expr,
      reductIsProper = False,
      reductStuck = stuck
    }
mkReduct _ (Just (expr, p), stuck) =
  Reduct
    { reductExpr = expr,
      reductIsProper = p,
      reductStuck = stuck
    }

-- | Reduce a core expression as much as possible.
reduce :: forall es. (Member (Reader Context) es) => CoreExpr -> Eff es Reduct
reduce expr = mkReduct expr <$> runState Nothing (makeChoiceA $ runState False (go expr []))
  where
    -- Reduce a core expression under a number of arguments.
    go :: CoreExpr -> [CoreArg] -> Eff (State Bool ': NonDet ': State (Maybe Id) ': es) CoreExpr
    go (Var x) args = do
      Context {contextBoundVars, contextFreeVars} <- ask
      case lookupVarEnv contextBoundVars x of
        Nothing
          | isDataConWorkId x ->
            pure (mkApps (Var x) args)
          | elemVarSet x contextFreeVars -> do
            put (Just x) -- Mark @x@ as a needed variable
            pure (mkApps (Var x) args)
          | otherwise -> pprPanic "Variable not in scope!" (ppr x)
        Just defn ->
          ( do
              put True -- Mark a reduction step
              go defn args
          )
            <|> pure (mkApps (Var x) args)
    go (Lit lit) [] = pure (Lit lit)
    go (App fun arg) args = go fun (arg : args)
    go (Lam x body) [] = empty
    go (Lam x body) (arg : args) = do
      Context {contextInScopeSet} <- ask
      let subst = mkOpenSubst contextInScopeSet [(x, arg)]
      put True
      go (substExpr subst body) args
    go (Let bind body) [] =
      Let bind <$> local (extendContextBind bind) (go body [])
    go (Case scrut x ty alts) [] = do
      Context {contextInScopeSet} <- ask
      scrut' <- go scrut []
      case scrut' of
        ConApp con args
          | Just (_, patVars, rhs) <- findAlt (DataAlt con) alts -> do
            let subst = mkOpenSubst contextInScopeSet ((x, scrut') : zip patVars (filter isValArg args))
            put True
            go (substExpr subst rhs) []
        Lit' lit
          | Just (_, [], rhs) <- findAlt (LitAlt lit) alts -> do
            put True
            go rhs []
        nonCon -> empty
    go (Type ty) args = pure (mkApps (Type ty) args)
    go expr' args = pprPanic "Could not reduce expression!" (ppr (mkApps expr' args))

-- * Pattern Utilities

-- | Core expressions that are the application of a data constructor to several arguments.
pattern ConApp :: DataCon -> [CoreArg] -> CoreExpr
pattern ConApp con args <-
  (viewConApp -> Just (con, args))
  where
    ConApp con args = mkCoreConApps con args

viewConApp :: CoreExpr -> Maybe (DataCon, [CoreArg])
viewConApp = go [] []
  where
    go binds args (Var x) = do
      con <- isDataConWorkId_maybe x
      pure (con, fmap (\arg -> foldr Let arg binds) args)
    go binds args (App fun arg) = go binds (arg : args) fun
    go binds [] (Let bind body) = go (bind : binds) [] body
    go _ _ _ = Nothing

-- | Core expressions that are literals under a number of let-bindings.
pattern Lit' :: Literal -> CoreExpr
pattern Lit' lit <-
  (viewLit -> Just lit)
  where
    Lit' lit = Lit lit

viewLit :: CoreExpr -> Maybe Literal
viewLit (Lit lit) = Just lit
viewLit (Let _ body) = viewLit body
viewLit _ = Nothing
