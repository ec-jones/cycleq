{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Normalisation
  ( -- * Reduction Context
    Context (..),
    progContext,
    addBind,
    addFreeVars,

    -- * Reduction
    normaliseTerm,
    criticalTerms,

    -- * Equation Simplification
    SimplifyRes (..),
    simplifyEquation,
    simplifySequent,
  )
where

import Control.Applicative
import Control.Monad.Reader
import Data.Bifunctor
import qualified Data.List as List
import GHC.Data.Maybe
import GHC.Plugins hiding (empty)
import Syntax hiding (criticalTerms, normaliseTerm, simplifyEquation, simplifySequent)

-- * Reduction Context

-- | A normalisation context is a collection of partially bound variables.
data Context = Context
  { -- | Bound variables.
    boundVars :: VarEnv CoreExpr,
    -- | The overvall set of variables in scope.
    inScopeSet :: InScopeSet
  }

-- | The initial context of a program.
progContext :: CoreProgram -> Context
progContext prog =
  Context
    { boundVars = mkVarEnv (second decodeCore <$> flattenBinds prog),
      inScopeSet = mkInScopeSet (mkVarSet (bindersOfBinds prog))
    }

-- | Extend a context with a binder.
addBind :: CoreBind -> Context -> Context
addBind bind ctx =
  ctx
    { boundVars = extendVarEnvList (boundVars ctx) (flattenBinds [bind]),
      inScopeSet = extendInScopeSetList (inScopeSet ctx) (bindersOf bind)
    }

-- | Extend the in scope set of a context with free variables.
addFreeVars :: [Var] -> Context -> Context
addFreeVars fvs ctx =
  ctx
    { inScopeSet = extendInScopeSetList (inScopeSet ctx) fvs
    }

-- * Reduction

-- | Normalise a core expression under a set of unconditional equations.
-- Equations are applied eagerly and so should be confluent.
normaliseTerm :: forall m. (MonadReader Context m) => [Equation] -> CoreExpr -> m CoreExpr
normaliseTerm equations expr = fromMaybe expr <$> runMaybeT (go expr [])
  where
    go :: CoreExpr -> [CoreArg] -> MaybeT m CoreExpr
    go (Var x) args
      | isDataConWorkId x = pure (mkApps (Var x) args)
      | otherwise = do
        ctx <- ask
        let xArgs = mkApps (Var x) args
        -- Match the expression against the left-hand side of equations
        case List.find (\(Equation lhs _) -> eqExpr (inScopeSet ctx) lhs xArgs) equations of
          Nothing
            | Just defn <- lookupVarEnv (boundVars ctx) x -> go defn args <|> pure xArgs
            | elemInScopeSet x (inScopeSet ctx) -> pure xArgs
            | otherwise -> pprPanic "variable not in scope!" (ppr x)
          Just (Equation _ rhs) -> go rhs []
    go (App fun arg) args = do
      arg' <- go arg [] <|> pure arg
      go fun (arg' : args)
    go (Lam x body) [] = empty
    go (Lam x body) (arg : args) = do
      scope <- asks inScopeSet
      let subst = mkOpenSubst scope [(x, arg)]
      go (substExpr subst body) args
    go (Let bind body) args =
      letConArgs bind <$> local (addBind bind) (go body args)
    go (Case scrut x ty alts) args = do
      scrut' <- go scrut []
      case collectArgs scrut' of
        (Var scrutHead, scrutArgs)
          | -- Find matching case alternative
            Just con <- isDataConWorkId_maybe scrutHead,
            Just (_, patVars, rhs) <- findAlt (DataAlt con) alts -> do
            scope <- asks inScopeSet
            let subst = mkOpenSubst scope ((x, scrut') : zip patVars (filter isValArg scrutArgs))
            go (substExpr subst rhs) args
        nonCon ->
          -- Scrutinee doesn't normalise to a constructor
          empty
    go _ _ =
      pprPanic "core expression must be stripped of ticks, casts, types, and coercions!" (text "")

-- | Push let binders under constructors
letConArgs :: CoreBind -> CoreExpr -> CoreExpr
letConArgs bind = go
  where
    go body =
      case collectArgs body of
        (Var con, args)
          | isDataConWorkId con -> mkApps (Var con) (fmap go args)
        nonCon -> Let bind body

-- | Recursively analyse which expressions are preventing reduction to a constructor.
criticalTerms :: forall m. (MonadReader Context m) => [Equation] -> CoreExpr -> m [CoreExpr]
criticalTerms equations expr = go expr []
  where
    go :: CoreExpr -> [CoreArg] -> m [CoreExpr]
    go (Var x) args
      | isDataConWorkId x = pure []
      | otherwise = do
        ctx <- ask
        let xArgs = mkApps (Var x) args
        -- Match the expression against the left-hand side of equations
        case List.find (\(Equation lhs _) -> eqExpr (inScopeSet ctx) lhs xArgs) equations of
          Nothing
            | Just defn <- lookupVarEnv (boundVars ctx) x -> go defn args
            | elemInScopeSet x (inScopeSet ctx) -> pure [xArgs]
            | otherwise -> pprPanic "variable not in scope!" (ppr x)
          Just (Equation _ rhs) -> go rhs []
    go (App fun arg) args =
      go fun (arg : args)
    go (Lam x body) [] = pure [Lam x body]
    go (Lam x body) (arg : args) = do
      scope <- asks inScopeSet
      let subst = mkOpenSubst scope [(x, arg)]
      go (substExpr subst body) args
    go (Let bind body) args =
      fmap (Let bind) <$> local (addBind bind) (go body args)
    go (Case scrut x ty alts) args = do
      scrut' <- normaliseTerm equations scrut
      -- Transitivity of critical terms
      scruts <- go scrut' []
      case collectArgs scrut' of
        (Var scrutHead, scrutArgs)
          | -- Find matching case alternative
            Just con <- isDataConWorkId_maybe scrutHead,
            Just (_, patVars, rhs) <- findAlt (DataAlt con) alts -> do
            scope <- asks inScopeSet
            let subst = mkOpenSubst scope ((x, scrut') : zip patVars (filter isValArg scrutArgs))
            go (substExpr subst rhs) args
          | [] <- scrutArgs -> pure scruts
        nonCon -> pure (scrut' : scruts)
    go _ _ =
      pprPanic "core expression must be stripped of ticks, casts, types, and coercions!" (text "")

-- * Equation Simplification

-- | The result of simplifying an equation.
data SimplifyRes a
  = Unsat
  | Trivial
  | Cong [a]
  | Reduce a
  deriving stock Functor

instance Outputable a => Outputable (SimplifyRes a) where
  ppr Unsat = text "Unsat"
  ppr Trivial = text "Trivial"
  ppr (Cong eqs) = text "Cong:" <+> ppr eqs
  ppr (Reduce eq) = text "Reduce:" <+> ppr eq

-- | One-step simplification of an equation.
simplifyEquation :: (MonadReader Context m) => [Equation] -> Equation -> m (SimplifyRes Equation)
simplifyEquation equations (Equation lhs rhs) = do
  lhs' <- normaliseTerm equations lhs
  rhs' <- normaliseTerm equations rhs
  scope <- asks inScopeSet
  pure (mkSimplifyResult scope lhs' rhs')
  where
    mkSimplifyResult scope lhs' rhs'
      | eqExpr scope lhs' rhs' = Trivial
      | (Var lcon, lconArgs) <- collectArgs lhs',
        (Var rcon, rconArgs) <- collectArgs rhs',
        isDataConWorkId lcon,
        isDataConWorkId rcon =
        if lcon == rcon
          then Cong (zipWith Equation lconArgs rconArgs)
          else Unsat
      | otherwise = Reduce (Equation lhs' rhs')

-- | Repeatedly simplify a sequents antecedent and consequent. 
simplifySequent :: MonadReader Context m => Sequent Equation -> m (SimplifyRes (Sequent Equation))
simplifySequent sequent = local (addFreeVars (univVars sequent)) $ go [] (antecedent sequent)
  where
    -- Simplify consequent under simplified antecedent.
    go acc [] = do
      consequent' <- simplifyEquation acc (consequent sequent)
      fmap
        ( \consequent' ->
            sequent
              { antecedent = acc,
                consequent = consequent'
              }
        )
        <$> simplifyEquation acc (consequent sequent)
    -- Simplify antecedent by focusing on each equation in turn.
    go acc (eq : eqs) = do
      res <- simplifyEquation (acc ++ eqs) eq
      case res of
        Unsat -> pure Trivial
        Trivial -> go acc eqs
        Cong eqs' -> go [] (eqs' ++ acc ++ eqs)
        Reduce eq -> go (eq : acc) eqs
