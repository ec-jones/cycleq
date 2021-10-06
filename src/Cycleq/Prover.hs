{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Module: Cycleq.Prover
module Cycleq.Prover (prover) where

import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Reader
import Control.Monad.State
import Cycleq.Edge
import Cycleq.Environment
import Cycleq.Equation
import Cycleq.Proof
import Cycleq.Reduction
import qualified Data.List as List
import GHC.Core.TyCo.Rep
import GHC.Plugins hiding (empty)

-- | Breadth-first search for a proof up-to a fixed depth.
prover ::
  Equation ->
  ReaderT ProgramEnv CoreM (Maybe Proof)
prover equation = do
  let proof = initProof [] [equation]
  go [(10, proof)]
  where
    go :: [(Int, Proof)] -> ReaderT ProgramEnv CoreM (Maybe Proof)
    go [] = pure Nothing
    go ((fuel, proof) : proofs)
      | fuel <= 0 = pure (Just proof) --  go proofs
      | otherwise = do
        proofs' <- runProverM proof step
        case List.find (null . proofIncompleteNodes) proofs' of
          Nothing -> go (proofs ++ fmap (fuel - 1,) proofs')
          Just proof' -> pure (Just proof')

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
  getUniqueSupplyM = ProverM $ lift $ lift $ lift $ getUniqueSupplyM

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

-- | Expand a partial proof tree.
step :: ProverM ProgramEnv ()
step = do
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
          -- TODO: Check if equation is absurd
          -- Reduce
          node' <- insertNode equation'
          insertEdge (identityEdge equation equation') (nodeId node) (nodeId node')

          -- pprTraceM "Reduct:" (ppr [node'])
          step
        Right stuckOn ->
          do
            -- Reflexivity
            refl equation

            -- pprTraceM "Refl:" (ppr ([] :: [Node]))
            step
            `cut` do
              -- Congruence
              equations' <- consCong equation
              nodes <-
                mapM
                  ( \equation' -> do
                      node' <- insertNode equation'
                      insertEdge (identityEdge equation equation') (nodeId node) (nodeId node')
                      pure node'
                  )
                  equations'
              -- pprTraceM "Cong:" (ppr nodes)
              step
            `cut` do
              -- Function Extensionality
              markNodeAsLemma node
              equation' <- funExt equation
              node' <- insertNode equation'
              insertEdge (identityEdge equation equation') (nodeId node) (nodeId node')

              -- pprTraceM "FunExt:" (ppr [node'])
              step
            `cut` ( do
                      -- Superposition
                      -- Select a lemma node
                      node' <- gets proofLemmas >>= msum . fmap pure
                      let equation' = nodeEquation node'

                      -- Rewrite current goal
                      (subst, equation'') <- superpose equation equation'
                      node'' <- insertNode equation''

                      -- Add edges
                      insertEdge (identityEdge equation equation'') (nodeId node) (nodeId node'')
                      insertEdge (substEdge subst equation equation') (nodeId node) (nodeId node')

                      -- pprTraceM "Super:" (ppr [node', node''])
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
                                        scope <- asks (envInScopeSet . intoEquationEnv xs)
                                        let subst = mkOpenSubst scope [(x, mkConApp2 k tyargs fresh)]
                                            equation' =
                                              Equation
                                                (fresh ++ (x `List.delete` xs))
                                                (substExpr subst lhs)
                                                (substExpr subst rhs)
                                        node' <- insertNode equation'
                                        insertEdge (caseEdge x fresh equation equation') (nodeId node) (nodeId node')
                                        pure node'
                                    )

                              pure ()
                            -- pprTraceM "Case:" (ppr nodes')
                            | otherwise -> empty
                  )

-- | Try to reduce either side of an equation.
reduceEquation :: Equation -> ProverM ProgramEnv (Either Equation (Maybe Id))
reduceEquation (Equation xs lhs rhs) = withEnv (intoEquationEnv xs) $ do
  (equation, isProper, stuckOn) <- runReductT $ do
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
  runReaderT (execStateT (go expr1 expr2) (mkEmptySubst scope)) (mkRnEnv2 scope)
  where
    go :: CoreExpr -> CoreExpr -> StateT Subst (ReaderT RnEnv2 (ProverM env)) ()
    go (Var x) e
      | x `elem` univs = modify (\subst -> extendIdSubst subst x e)
      | Var y <- e = do
        env <- ask
        unless
          (rnOccL env x == rnOccR env y)
          empty
    go (Lit lit1) (Lit lit2)
      | lit1 == lit2 = pure ()
      | otherwise = empty
    go (App fun1 arg1) (App fun2 arg2) = do
      go fun1 fun2
      when (isValArg arg1) (go arg1 arg2)
    go (Lam x1 body1) (Lam x2 body2) =
      local
        (\env -> rnBndr2 env x1 x2)
        (go body1 body2)
    go (Let bndr1 body1) (Let bndr2 body2) =
      let (xs1, defns1) = unzip (flattenBinds [bndr1])
          (xs2, defns2) = unzip (flattenBinds [bndr2])
       in local (\env -> rnBndrs2 env xs1 xs2) $ do
            zipWithM_ go defns1 defns2
            go body1 body2
    go _ _ = empty
