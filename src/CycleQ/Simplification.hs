module CycleQ.Simplification
  ( Result (..),
    simplifyClause,
    simplifyEquations,
    solveEquations,
  )
where

import Control.Applicative
import Control.Monad.State
import CycleQ.Reduction
import CycleQ.Syntax
import CycleQ.Unique.Fresh
import Data.Map qualified as Map

-- | The result of simplifying an equation or a clause.
data Result a
  = Refl
  | Absurd a
  | Cong [a]
  | FunEx Type (Var -> a)
  | Reduce a
  | Stuck a
  deriving stock (Functor)

-- | Simplify a clause using reflexivity and congruence.
simplifyClause :: (?program :: Program) => Clause -> ([Equation], Result Clause)
simplifyClause clause =
  case simplifyHypotheses
    (clauseVars clause)
    (clauseHypRules clause)
    (clauseHypEqs clause) of
    Nothing -> ([], Refl)
    Just (hypotheses, equations)
      | Just (Equation _ lhs rhs) <- clauseGoal clause,
        FunTy argTy resTy <- exprType lhs ->
          -- Function extensionality
          ( equations,
            FunEx argTy $ \x ->
              let arg = Var x []
               in clause
                    { clauseVars = x : clauseVars clause,
                      clauseHypRules = hypotheses,
                      clauseHypEqs = equations,
                      clauseGoal = Just (mkEquation (App lhs arg) (App rhs arg))
                    }
          )
      | Just goal <- clauseGoal clause ->
          let ?hypotheses = hypotheses
           in ( equations,
                fmap
                  ( \goal' ->
                      clause
                        { clauseHypRules = hypotheses,
                          clauseHypEqs = equations,
                          clauseGoal = Just goal'
                        }
                  )
                  (simplifyEquation goal)
              )
      | otherwise ->
          ( equations,
            Stuck
              clause
                { clauseHypRules = hypotheses,
                  clauseHypEqs = equations
                }
          )

-- | Simplify a set of equation using reduction, reflexivity and congruence.
simplifyEquations ::
  ( ?program :: Program,
    ?hypotheses :: Hypotheses
  ) =>
  [Equation] ->
  Maybe [Equation]
simplifyEquations [] = Just []
simplifyEquations (eq : eqs) =
  case simplifyEquation eq of
    Refl -> simplifyEquations eqs
    Absurd _ -> Nothing
    Cong eqs' -> simplifyEquations (eqs' ++ eqs)
    FunEx _ _ ->
      error "Cannot apply function extensionality to simplify equations!"
    Reduce eq' ->
      simplifyEquations (eq' : eqs)
    Stuck eq' -> do
      eqs' <- simplifyEquations eqs
      pure (eq' : eqs')

-- | Simplify an equation using reduction, reflexivity and congruence.
simplifyEquation ::
  ( ?program :: Program,
    ?hypotheses :: Hypotheses
  ) =>
  Equation ->
  Result Equation
simplifyEquation eq@(Equation _ lhs rhs)
  | lhs == rhs = Refl -- Reflexivity
  | Just (con, _, conArgs) <- viewConApp lhs,
    Just (con', _, conArgs') <- viewConApp rhs =
      -- Congruence/Absurd
      if con == con'
        then Cong (zipWith mkEquation conArgs conArgs')
        else Absurd eq
  | Lit lit <- lhs,
    Lit lit' <- rhs =
      -- Congruence/Absurd
      if lit == lit'
        then Refl -- The only literal arguments are for "rubbish" literals.
        else Absurd eq
  | otherwise =
      -- Reduction/Stuck
      let (p, lhsCriticals, lhs') = reduceWithCriticals lhs
          (q, rhsCriticals, rhs') = reduceWithCriticals rhs
       in if p || q
            then Reduce (Equation (lhsCriticals <> rhsCriticals) lhs' rhs')
            else Stuck (Equation (lhsCriticals <> rhsCriticals) lhs' rhs')

-- | Repeatedly simplify a list of equations into a confluent expression map.
simplifyHypotheses ::
  (?program :: Program) =>
  [Var] ->
  Hypotheses -> -- \^ Oriented hypotheses
  [Equation] -> -- \^ Unorientated hypotheses
  Maybe
    ( Hypotheses, -- \^ Combined hypotheses
      [Equation] -- \^ Remaining equations that cannot be orientated
    )
simplifyHypotheses xs hyps [] = pure (hyps, [])
simplifyHypotheses xs hyps (eq : eqs) =
  case let ?hypotheses = hyps
        in simplifyEquation eq of
    Refl ->
      simplifyHypotheses xs hyps eqs
    Absurd _ -> Nothing
    Cong eqs' ->
      simplifyHypotheses xs hyps (eqs' ++ eqs)
    FunEx _ _ ->
      error "Cannot apply function extensionality to hypotheses!"
    Reduce eq' ->
      simplifyHypotheses xs hyps (eq' : eqs)
    Stuck eq' -> do
      case orientEquation xs eq' of
        Nothing
          | null eqs -> pure (hyps, [eq'])
          | otherwise -> do
              (hyps', eqs') <- simplifyHypotheses xs hyps eqs
              revisit eq' hyps' eqs'
        Just oriented@(Equation _ lhs rhs) -> do
          -- Re-simplify existing hypotheses ...
          let (overlaps, hyps') =
                foldr
                  collapse
                  ( [],
                    [oriented]  -- ... under the new hypothesis
                  )
                  hyps

          -- Revist those that are no longer joinable
          simplifyHypotheses xs hyps' (overlaps ++ eqs)
  where
    -- Attempt to simplify an equation for a second time.
    -- If it is still stuck, we are done.
    -- Otherwise, we must revist all equations.
    revisit :: Equation -> Hypotheses -> [Equation] -> Maybe (Hypotheses, [Equation])
    revisit eq hyps eqs =
      case let ?hypotheses = hyps
            in simplifyEquation eq of
        Refl -> pure (hyps, eqs)
        Absurd _ -> Nothing
        Cong eqs' ->
          simplifyHypotheses xs hyps (eqs' ++ eqs)
        FunEx _ _ ->
          error "Cannot apply function extensionality to hypotheses!"
        Reduce eq' ->
          simplifyHypotheses xs hyps (eq' : eqs)
        Stuck eq' ->
          pure (hyps, eq' : eqs)

    -- Re-simplify existing hypotheses
    collapse :: Equation -> ([Equation], Hypotheses) -> ([Equation], Hypotheses)
    collapse (Equation criticals lhs rhs) (overlaps, hyps) =
      let ?hypotheses = hyps
       in case reduceWithCriticals lhs of
            (True, _, lhs') ->
              -- Critical Overlap!
              ( Equation criticals lhs' (reduce rhs) : overlaps,
                hyps
              )
            (False, _, _)
              -- | lhs `Map.member` hyps -> error "Hypothesis overlap!"
              | otherwise ->
                  ( overlaps,
                    Equation criticals lhs (reduce rhs) : hyps
                  )

-- | Orientate equations according to precedence ordering.
-- This function returns @Nothing@ if the larger expression is not stable.
orientEquation :: (?program :: Program) => [Var] -> Equation -> Maybe Equation
orientEquation xs (Equation criticals lhs rhs) = do
  compareExpr lhs rhs >>= \case
    LT
      | isStable rhs 0 -> Just (Equation criticals rhs lhs)
      | otherwise -> Nothing
    EQ -> error "Failed to simplify equation!"
    GT
      | isStable lhs 0 -> Just (Equation criticals lhs rhs)
      | otherwise -> Nothing
  where
    isStable :: Expr -> Int -> Bool
    isStable (Var x tyArgs) n
      | x `elem` xs = True
      | otherwise =
          isFirstOrder (instantiatePolyType (varType x) tyArgs) n
    isStable (Con _ _) _ = False
    isStable (Lit _) _ = False
    isStable (App fun arg) n =
      isStable fun (n + 1)

    isFirstOrder :: Type -> Int -> Bool
    isFirstOrder (TyVar _ _) _ = True
    isFirstOrder (DataTy _ _) _ = True
    isFirstOrder (FunTy _ resTy) n
      | n <= 0 = False
      | otherwise = isFirstOrder resTy (n - 1)
    isFirstOrder (LitTy _) _ = True
    isFirstOrder _ _ =
      error "Expected a type!"

-- | Attempt to unify a set of equations using one-sided paramodulation.
solveEquations ::
  forall m.
  ( ?program :: Program,
    ?hypotheses :: Hypotheses,
    MonadPlus m,
    MonadFresh m
  ) =>
  [TyVar] -> -- \^ Unification type variables
  [Var] -> -- \^ Unification variables
  [Equation] ->
  TySubst ->
  Subst ->
  m (TySubst, Subst)
solveEquations as xs = curry . execStateT . mapM_ go
  where
    go :: Equation -> StateT (TySubst, Subst) m ()
    go eq = do
      (tyTheta, theta) <- get
      case simplifyEquation (substEquation tyTheta theta eq) of
        Refl -> pure ()
        Cong eqs -> mapM_ go eqs
        Absurd _ -> empty
        FunEx _ _ ->
          -- Function extensionality is actually fine here but best to keep things simple.
          error "Unexpected function extensionality!"
        Reduce eq' -> go eq' -- Maybe a simplification will now apply
        Stuck (Equation _ lhs rhs)
          | Var x [] <- lhs -> do
              -- Eliminate
              guard
                ( x
                    `elem` xs
                    && x
                    `occCheck` rhs
                )
              put (tyTheta, Map.insert x rhs theta)
          | App fun arg <- lhs ->
              ( do
                  case rhs of
                    Var y _
                      | y `elem` xs ->
                          case Map.lookup y theta of
                            Nothing -> do
                              -- Imitate
                              (residuals, rhs') <- imitate lhs
                              put (tyTheta, Map.insert y rhs' theta)

                              mapM_ (\(lhs, y') -> go (mkEquation lhs (Var y' []))) residuals
                            Just rhs' -> do
                              go (mkEquation lhs rhs')
                    App fun' arg' -> do
                      -- Decompose
                      go (mkEquation fun fun')
                      go (mkEquation arg arg')
                    noDecomp -> empty
              )
                <|> ( do
                        -- Mutate
                        Equation _ lhs' rhs' <- asum (pure <$> ?hypotheses)
                        case lhs' of
                          App fun' arg'
                            | Just tyTheta' <-
                                -- Ensure types match
                                matchType
                                  (filter (`Map.notMember` tyTheta) as)
                                  (exprType rhs)
                                  (exprType lhs') -> do
                                put (tyTheta <> tyTheta', theta)

                                go (mkEquation fun fun')
                                go (mkEquation arg arg')
                                go (mkEquation rhs' rhs)
                          noMutation -> empty
                    )
          | otherwise -> empty

    imitate :: Expr -> StateT (TySubst, Subst) m ([(Expr, Var)], Expr)
    imitate var@(Var x _)
      | x `notElem` xs = pure ([], var)
      | otherwise = empty
    imitate con@(Con _ _) = pure ([], con)
    imitate lit@(Lit _) = pure ([], lit)
    imitate (App fun arg) = do
      fun' <- freshVar (exprType fun)
      arg' <- freshVar (exprType arg)

      pure
        ( [(fun, fun'), (arg, arg')],
          App (Var fun' []) (Var arg' [])
        )

    occCheck :: Var -> Expr -> Bool
    occCheck x (Var y _) = x /= y
    occCheck x (Con con _) = True
    occCheck x (Lit _) = True
    occCheck x (App fun arg) =
      occCheck x fun && occCheck x arg
