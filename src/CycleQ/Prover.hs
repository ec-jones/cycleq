{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Module: Cycleq.Prover
module CycleQ.Prover
  ( ProverState (..),
    prover,
  )
where

import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import CycleQ.Edge
import CycleQ.Environment
import CycleQ.Equation
import qualified CycleQ.Proof as Proof
import CycleQ.Reduction
import Data.Bifunctor
import qualified Data.List as List
import GHC.Core.TyCo.Rep
import GHC.Plugins hiding (empty, trace)
import System.CPUTime

-- | State of the proof search engine.
data ProverState = ProverState
  { -- | Remaining fuel
    proverFuel :: Int,
    -- | Partial proof graph
    proofGraph :: !Proof.Proof,
    -- | Nodes suitable for superposition
    lemmaNodes :: [Int],
    -- | Unjustified nodes
    goalNodes :: [Int]
  }

-- | Initialise prover state.
initProver :: Int -> [Equation] -> [Equation] -> ProverState
initProver fuel lemmas goals =
  let (proof, ids) = List.mapAccumL (flip Proof.insertNode) Proof.emptyProof (lemmas ++ goals)
      (lemmaIds, goalIds) = splitAt (length lemmas) ids
   in ProverState fuel proof lemmaIds goalIds

-- | Decrease the state's fuel.
decreaseFuel :: ProverState -> ProverState
decreaseFuel st = st {proverFuel = proverFuel st - 1}

-- | Insert a new equation into a ProverState's proof graph.
insertNode :: Equation -> ProverM env Int
insertNode equation = state $ \st ->
  let (proof, nodeId) = Proof.insertNode equation (proofGraph st)
   in (nodeId, st {goalNodes = nodeId : goalNodes st, proofGraph = proof})

-- | Mark a node as suitable for superposition.
markNodeAsLemma :: Int -> ProverM env ()
markNodeAsLemma i = modify $ \st ->
  st {lemmaNodes = List.insert i (lemmaNodes st)}

-- | Insert edge into ProverState's proof graph recording the time ellapsed.
insertEdge :: Int -> Int -> Edge -> ProverM env ()
insertEdge source target edge = do
  st <- get
  t0 <- liftIO getCPUTime
  let proof = Proof.insertEdge source target edge (proofGraph st)
  guard (Proof.proofWellFounded proof)
  t1 <- liftIO getCPUTime
  tell (Sum (t1 - t0))
  put
    st {proofGraph = proof}

-- | Find the next unjustified node to expand.
popGoal :: ProverM env (Maybe Int)
popGoal = do
  st <- get
  case goalNodes st of
    [] -> pure Nothing
    (goal : goals) -> do
      put st {goalNodes = goals}
      pure (Just goal)

-- | Breadth-first search for a proof up-to a fixed depth.
prover ::
  ProgramEnv ->
  Int ->
  [Equation] ->
  [Equation] ->
  CoreM (Maybe ProverState, Sum Integer)
prover env fuel lemmas goals = runWriterT $ runReaderT (go [initProver fuel lemmas goals]) env
  where
    go :: [ProverState] -> ReaderT ProgramEnv (WriterT (Sum Integer) CoreM) (Maybe ProverState)
    go [] = pure Nothing
    go stss@(st : sts)
      | null (goalNodes st) = pure (Just st)
      | proverFuel st <= 0 = go sts
      | otherwise = do
        nextStates <- runProverM st (expand False)
        go (fmap decreaseFuel nextStates ++ sts)

-- | Expand a proof tree.
expand :: Bool -> ProverM ProgramEnv ()
expand trace = do
  popGoal >>= \case
    Nothing -> pure ()
    Just goalNode -> do
      ProverState {lemmaNodes = lemmas, proofGraph = proof} <- get
      let goalEquation@(Equation xs lhs rhs) = Proof.lookupNode goalNode proof

      when trace $
        pprTraceM ("Goal " ++ show goalNode ++ ":") (ppr goalEquation)

      reduceEquation goalEquation >>= \case
        Left reductEquation -> do
          goalNode' <- insertNode reductEquation
          insertEdge goalNode goalNode' (identityEdge goalEquation reductEquation)

          when trace $
            pprTraceM "Reduce:" (ppr [goalNode'])

          expand trace
        Right stuckOn ->
          ( do
              -- Reflexivity
              refl goalEquation

              when trace $
                pprTraceM "Refl:" (ppr ([] :: [Int]))

              expand trace
          )
            `cut` ( do
                      -- Congruence
                      goalEquations' <- consCong goalEquation
                      goalNodes' <-
                        mapM
                          ( \goalEquation' -> do
                              goalNode' <- insertNode goalEquation'
                              insertEdge goalNode goalNode' (identityEdge goalEquation goalEquation')
                              pure goalNode'
                          )
                          goalEquations'

                      when trace $
                        pprTraceM "Cong:" (ppr goalNodes')

                      expand trace
                  )
            `cut` ( do
                      -- Function Extensionality
                      markNodeAsLemma goalNode
                      goalEquation' <- funExt goalEquation
                      goalNode' <- insertNode goalEquation'
                      insertEdge goalNode goalNode' (identityEdge goalEquation goalEquation')

                      when trace $
                        pprTraceM "FunExt:" (ppr [goalNode'])

                      expand trace
                  )
            `cut` ( do
                      -- Superposition
                      lemmaNode <- msum (fmap pure lemmas) -- Select a lemma node
                      let lemmaEquation = Proof.lookupNode lemmaNode proof

                      -- Rewrite current goal
                      (subst, goalEquation') <- superpose goalEquation lemmaEquation
                      goalNode' <- insertNode goalEquation'

                      -- Add edges
                      insertEdge goalNode goalNode' (identityEdge goalEquation goalEquation')
                      insertEdge goalNode lemmaNode (substEdge subst goalEquation lemmaEquation)

                      when trace $
                        pprTraceM "Super:" (ppr [lemmaNode, goalNode'])
                      <|> do
                        -- Case analysis
                        markNodeAsLemma goalNode
                        case stuckOn of
                          Nothing -> empty
                          Just x
                            | TyConApp dty tyargs <- idType x -> do
                              goalNodes' <-
                                casesOf dty tyargs
                                  >>= mapM
                                    ( \(k, fresh) -> do
                                        let scope = mkInScopeSet (mkVarSet fresh)
                                            subst = mkOpenSubst scope [(x, mkConApp2 k tyargs fresh)]
                                            goalEquation' =
                                              Equation
                                                (fresh ++ (x `List.delete` xs))
                                                (substExpr subst lhs)
                                                (substExpr subst rhs)
                                        goalNode' <- insertNode goalEquation'
                                        insertEdge goalNode goalNode' (caseEdge x fresh goalEquation goalEquation')
                                        pure goalNode'
                                    )

                              when trace $
                                pprTraceM "Case:" (ppr goalNodes')
                            | otherwise -> empty
                  )

-- | Try to reduce either side of an equation.
reduceEquation :: Equation -> ProverM ProgramEnv (Either Equation (Maybe Id))
reduceEquation goal@(Equation xs lhs rhs) = do
  scope <- asks progInScopeSet
  withEnv (intoEquationEnv xs) $ do
    (equation, isProper, stuckOn) <- runReductT goal $ do
      lhs' <- reduce lhs
      rhs' <- reduce rhs
      pure (Equation xs lhs' rhs')
    pure $
      if isProper
        then Left (prune (getInScopeVars scope) equation)
        else Right stuckOn

-- -- | Fail if an equation is absurd.
-- checkNotAbsurd :: Equation -> ProverM env ()
-- checkNotAbsurd (Equation xs lhs rhs) =
--   case (,) <$> viewNormalForm lhs <*> viewNormalForm rhs of
--     Just (Left (con, args), Left (con', args'))
--       | con /= con' -> empty
--     Just (Right lit, Right lit')
--       | lit /= lit' -> empty
--     nonMatch -> pure ()

-- | Reflexivity
refl :: Equation -> ProverM ProgramEnv ()
refl (Equation xs lhs rhs) = do
  scope <- asks (envInScopeSet . intoEquationEnv xs)
  guard (eqExpr scope lhs rhs)

-- | Decompose an equation by congruence if both sides are headed by a constructor or literal.
consCong :: Equation -> ProverM ProgramEnv [Equation]
consCong (Equation xs lhs rhs) = do
  scope <- asks progInScopeSet
  case (,) <$> viewNormalForm lhs <*> viewNormalForm rhs of
    Just (Left (con, args), Left (con', args'))
      | con == con' -> pure (prune (getInScopeVars scope) <$> zipWith (Equation xs) args args')
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
  progScope <- asks progInScopeSet
  scope <- asks (envInScopeSet . intoEquationEnv xs)
  sub <- equationSubExprs goal
  guard (not (isVariableSubExpr sub))
  second (prune (getInScopeVars progScope))
    <$> withSubExpr
      sub
      ( \expr ->
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
      )
  where
    isNonVar (Var _) = False
    isNonVar _ = True

-- | Find an instance of the first expression that is alpha equivalent to the second.
match :: [Id] -> InScopeSet -> CoreExpr -> CoreExpr -> ProverM ProgramEnv Subst
match univs scope expr1 expr2 = do
  guard (eqType (exprType expr1) (exprType expr2))
  subst@(Subst _ idenv _ _) <- runReaderT (execStateT (go expr1 expr2) (mkEmptySubst scope)) (mkRnEnv2 scope)
  guard (all (`elemVarEnv` idenv) univs)
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

-- * ProverM monad transformer

-- | The ProverM monad non-deterministically manipulate a proof.
newtype ProverM env a = ProverM
  { unProverM :: ReaderT env (StateT ProverState (LogicT (WriterT (Sum Integer) CoreM))) a
  }
  deriving newtype
    ( Functor,
      Applicative,
      Alternative,
      Monad,
      MonadPlus,
      MonadReader env,
      MonadState ProverState,
      MonadLogic
    )

instance MonadWriter (Sum Integer) (ProverM env) where
  tell delta = ProverM $ lift $ lift $ lift $ tell delta

-- listen (ProverM m) = ProverM $
--   lift $ lift $ lift $ listen _

instance MonadUnique (ProverM env) where
  getUniqueSupplyM = ProverM $ lift $ lift $ lift $ lift getUniqueSupplyM

instance MonadIO (ProverM env) where
  liftIO m = ProverM $ liftIO m

-- -- | Lift a CoreM action into a ProverM.
-- liftCoreM :: CoreM a -> ProverM env a
-- liftCoreM m = ProverM $ lift $ lift $ lift $ lift m

-- | Evaluate a prover action on a proof.
runProverM :: ProverState -> ProverM env () -> ReaderT env (WriterT (Sum Integer) CoreM) [ProverState]
runProverM st = mapReaderT (observeAllT . flip execStateT st) . unProverM

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

infixr 9 `cut`