{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Module: Cycleq.Prover
module Cycleq.Prover (prover) where

import System.CPUTime
import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Reader
import Control.Monad.State
import Cycleq.Edge
import Cycleq.Environment
import Cycleq.Equation
import Cycleq.Proof
import Cycleq.Reduction
import Data.Bifunctor
import qualified Data.List as List
import GHC.Core.TyCo.Rep
import GHC.Plugins hiding (empty)

-- | Breadth-first search for a proof up-to a fixed depth.
prover ::
  Bool ->
  Equation ->
  ReaderT ProgramEnv CoreM (Maybe (Int, Proof))
prover redundantLemma equation = do
  let proof = initProof [] [equation]
  go [(10, proof)]
  where
    go :: [(Int, Proof)] -> ReaderT ProgramEnv CoreM (Maybe (Int, Proof))
    go [] = pure Nothing
    go ((fuel, proof) : proofs)
      | null (proofIncompleteNodes proof) = pure (Just (fuel, proof))
      | fuel <= 0 = go proofs
      | otherwise = do
        proofs' <- runProverM proof (step redundantLemma)
        case List.find (null . proofIncompleteNodes) proofs' of
          Nothing -> go (proofs ++ fmap (fuel - 1,) proofs')
          Just proof' -> pure (Just (fuel, proof'))

-- | The ProverM monad non-deterministically manipulate a proof.
newtype ProverM env a = ProverM
  { unProverM :: ReaderT env (StateT Proof (LogicT CoreM)) a
  }
  deriving newtype
    ( Functor,
      Applicative,
      Alternative,
      Monad,
      MonadPlus,
      MonadReader env,
      MonadState Proof,
      MonadLogic
    )

instance MonadUnique (ProverM env) where
  getUniqueSupplyM = ProverM $ lift $ lift $ lift getUniqueSupplyM

instance MonadIO (ProverM env) where
  liftIO m = ProverM $ liftIO m

-- | Lift a CoreM action into a ProverM.
liftCoreM :: CoreM a -> ProverM env a
liftCoreM m = ProverM $ lift $ lift $ lift m

-- | Evaluate a prover action on a proof.
runProverM :: Proof -> ProverM env () -> ReaderT env CoreM [Proof]
runProverM proof = mapReaderT (observeAllT . flip execStateT proof) . unProverM

-- | Change the reader environment of a Prover action.
withEnv :: (env' -> env) -> ProverM env a -> ProverM env' a
withEnv f (ProverM m) = ProverM (withReaderT f m)

-- | Take just the first result from the first action.
-- Otherwise, perform the second action.
cut :: MonadLogic m => m a -> m a -> m a
cut m1 m2 =
  msplit m1 >>= \case
    Nothing -> m2
    Just (res, _) -> pure res

infixr `cut`

-- | Expand a partial proof tree.
step :: Bool -> ProverM ProgramEnv ()
step redundantLemma = do
  proof <- get
  case proofIncompleteNodes proof of
    [] -> pure ()
    (node : _) -> do
      let equation@(Equation xs lhs rhs) = nodeEquation node
      -- TODO: Check if equation is absurd

      markNodeAsJustified node
      -- pprTraceM (show node ++ ":") (ppr equation)

      reduceEquation equation >>= \case
        Left equation' -> do
          -- Reduce
          when redundantLemma $ markNodeAsLemma node
          node' <- insertNode equation'
          t0 <- liftIO getCPUTime
          insertEdge (identityEdge equation equation') (nodeId node) (nodeId node')
          t1 <- liftIO getCPUTime
          edgeTime (t1 - t0)

          -- pprTraceM "Reduct:" (ppr [node'])
          step redundantLemma
        Right stuckOn -> do
          s <-
            ( do
                -- Reflexivity
                refl equation

                -- pprTraceM "Refl:" (ppr ([] :: [Node]))
                pure True
              )
              `cut` ( do
                        -- Congruence
                        when redundantLemma $ markNodeAsLemma node
                        equations' <- consCong equation
                        nodes <-
                          mapM
                            ( \equation' -> do
                                node' <- insertNode equation'
                                t0 <- liftIO getCPUTime
                                insertEdge (identityEdge equation equation') (nodeId node) (nodeId node')
                                t1 <- liftIO getCPUTime
                                edgeTime (t1 - t0)
                                pure node'
                            )
                            equations'
                        -- pprTraceM "Cong:" (ppr nodes)
                        pure True
                    )
              `cut` ( do
                        -- Function Extensionality
                        markNodeAsLemma node
                        equation' <- funExt equation
                        node' <- insertNode equation'
                        t0 <- liftIO getCPUTime
                        insertEdge (identityEdge equation equation') (nodeId node) (nodeId node')
                        t1 <- liftIO getCPUTime
                        edgeTime (t1 - t0)

                        -- pprTraceM "FunExt:" (ppr [node'])
                        pure True
                    )
              `cut` ( do
                        -- Superposition
                        when redundantLemma $ markNodeAsLemma node

                        -- Select a lemma node
                        node' <- gets proofLemmas >>= msum . fmap pure
                        let equation' = nodeEquation node'

                        -- Rewrite current goal
                        (subst, equation'') <- superpose equation equation'
                        node'' <- insertNode equation''

                        -- Add edges
                        t0 <- liftIO getCPUTime
                        insertEdge (identityEdge equation equation'') (nodeId node) (nodeId node'')
                        insertEdge (substEdge subst equation equation') (nodeId node) (nodeId node')
                        t1 <- liftIO getCPUTime
                        edgeTime (t1 - t0)

                        -- pprTraceM "Super:" (ppr [node', node''])
                        pure False
                        <|> do
                          -- Case analysis
                          markNodeAsLemma node
                          case stuckOn of
                            Nothing -> empty
                            Just x
                              | TyConApp dty tyargs <- idType x -> do
                                nodes' <-
                                  casesOf dty tyargs
                                    >>= mapM
                                      ( \(k, fresh) -> do
                                          let scope = mkInScopeSet (mkVarSet fresh)
                                              subst = mkOpenSubst scope [(x, mkConApp2 k tyargs fresh)]
                                              equation' =
                                                Equation
                                                  (fresh ++ (x `List.delete` xs))
                                                  (substExpr subst lhs)
                                                  (substExpr subst rhs)
                                          node' <- insertNode equation'
                                          t0 <- liftIO getCPUTime
                                          insertEdge (caseEdge x fresh equation equation') (nodeId node) (nodeId node')
                                          t1 <- liftIO getCPUTime
                                          edgeTime (t1 - t0)
                                          pure node'
                                      )

                                -- pprTraceM "Case:" (ppr nodes')
                                pure False
                              | otherwise -> empty
                    )
          when
            s
            (step redundantLemma)

-- | Try to reduce either side of an equation.
reduceEquation :: Equation -> ProverM ProgramEnv (Either Equation (Maybe Id))
reduceEquation goal@(Equation xs lhs rhs) = withEnv (intoEquationEnv xs) $ do
  (equation, isProper, stuckOn) <- runReductT goal $ do
    lhs' <- reduce lhs
    rhs' <- reduce rhs
    pure (Equation xs lhs' rhs')
  pure $
    if isProper
      then Left equation
      else Right stuckOn

-- | Reflexivity
refl :: Equation -> ProverM ProgramEnv ()
refl (Equation xs lhs rhs) = do
  scope <- asks (envInScopeSet . intoEquationEnv xs)
  guard (eqExpr scope lhs rhs)

-- | Decompose an equation by congruence if both sides are headed by a constructor or literal.
consCong :: Equation -> ProverM env [Equation]
consCong (Equation xs lhs rhs) =
  case (,) <$> viewNormalForm lhs <*> viewNormalForm rhs of
    Just (Left (con, args), Left (con', args'))
      | con == con' -> pure (zipWith (Equation xs) args args')
    Just (Right lit, Right lit')
      | lit == lit' -> pure []
    nonMatch -> empty

-- | Create a fresh variable as an argument to both sides.
funExt :: Equation -> ProverM env Equation
funExt (Equation xs lhs rhs) = do
  let ty = exprType lhs
  guard (isFunTy ty)
  x <- freshVar (funArgTy ty)
  pure $
    Equation (x : xs) (App lhs (Var x)) (App rhs (Var x))

-- | Generate a fresh instance for each possible constructor.
casesOf :: TyCon -> [Type] -> ProverM env [(DataCon, [Var])]
casesOf dty tyargs =
  mapM (\con -> (con,) <$> mapM freshVar (scaledThing <$> dataConInstArgTys con tyargs)) (tyConDataCons dty)

-- | Create a fresh variable of a given type.
freshVar :: Type -> ProverM env Id
freshVar ty = do
  unique <- getUniqueM
  let name = mkInternalName unique (mkVarOcc ("x_" ++ show unique)) (UnhelpfulSpan UnhelpfulGenerated)
  pure (mkLocalId name Many ty)

-- | Rewrite the first equation with an instance of the second.
superpose :: Equation -> Equation -> ProverM ProgramEnv (Subst, Equation)
superpose goal@(Equation xs _ _) lemma@(Equation ys lhs rhs) = do
  scope <- asks (envInScopeSet . intoEquationEnv xs)
  sub <- equationSubExprs goal
  guard (not (isVariableSubExpr sub))
  withSubExpr sub $ \expr ->
    ( do
        guard (isNonVar lhs)
        subst <- match ys scope lhs expr
        pure (subst, substExpr subst rhs)
    )
      <|> ( do
              guard (isNonVar rhs)
              subst <- match ys scope rhs expr
              pure (subst, substExpr subst lhs)
          )
  where
    isNonVar (Var _) = False
    isNonVar _ = True

-- | Find an instance of the first expression that is alpha equivalent to the second.
match :: [Id] -> InScopeSet -> CoreExpr -> CoreExpr -> ProverM ProgramEnv Subst
match univs scope expr1 expr2 = do
  guard (eqType (exprType expr1) (exprType expr2))
  subst@(Subst _ idenv _ _) <- runReaderT (execStateT (go expr1 expr2) (mkEmptySubst scope)) (mkRnEnv2 scope)
  guard (all (\x -> elemVarEnv x idenv) univs)
  pure subst
  where
    go :: CoreExpr -> CoreExpr -> StateT Subst (ReaderT RnEnv2 (ProverM env)) ()
    go (Var x) e
      | x `elem` univs = do
        subst@(Subst _ idenv _ _) <- get
        case lookupVarEnv idenv x of
          Nothing -> put (extendIdSubst subst x e)
          Just e' -> guard (cheapEqExpr e e')
      | Var y <- e = do
        env <- ask
        guard (rnOccL env x == rnOccR env y)
    go (Lit lit1) (Lit lit2) = guard (lit1 == lit2)
    go (App fun1 arg1) (App fun2 arg2) = do
      go fun1 fun2
      when (isValArg arg1) $
        go arg1 arg2
    go (Lam x1 body1) (Lam x2 body2) =
      local
        (\env -> rnBndr2 env x1 x2)
        (go body1 body2)
    go (Let bndr1 body1) (Let bndr2 body2) = do
      let (xs1, defns1) = unzip (flattenBinds [bndr1])
          (xs2, defns2) = unzip (flattenBinds [bndr2])
      local (\env -> rnBndrs2 env xs1 xs2) $ do
        zipWithM_ go defns1 defns2
        go body1 body2
    go (Case scrut1 x1 _ alts1) (Case scrut2 x2 _ alts2) = do
      go scrut1 scrut2
      local (\env -> rnBndr2 env x1 x2) $ do
        zipWithM_ goAlt alts1 alts2
    go _ _ = empty

    goAlt :: CoreAlt -> CoreAlt -> StateT Subst (ReaderT RnEnv2 (ProverM env)) ()
    goAlt (c1, bs1, e1) (c2, bs2, e2) = do
      guard (c1 == c2)
      local (\env -> rnBndrs2 env bs1 bs2) $
        go e1 e2
