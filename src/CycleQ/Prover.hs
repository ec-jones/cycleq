{-# LANGUAGE MultiParamTypeClasses #-}

module CycleQ.Prover
  ( ProverState (..),
    prover,
  )
where

import Control.Applicative
import Control.Monad.Logic
import Control.Monad.State
import Control.Monad.Writer
import CycleQ.Proof.Proof qualified as Proof
import CycleQ.Simplification
import CycleQ.Syntax
import CycleQ.Unique.Fresh
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Sequence qualified as Seq

-- | Attempt to construct a proof.
prover ::
  ( ?program :: Program,
    ?dataTypeEnv :: DataTypeEnv,
    ?online :: Bool,
    ?conditional :: Bool
  ) =>
  Int -> -- \^ Fuel
  [Clause] -> -- \^ Lemmas
  [Clause] -> -- \^ Goals
  (Maybe ProverState, [Equation])
prover fuel lemmas goals = go [] 0
  where
    go :: [Equation] -> Int -> (Maybe ProverState, [Equation])
    go acc depth
      | depth > fuel = (Nothing, acc)
      | otherwise =
        case runProver loop (initProver depth lemmas goals) of
          (Nothing, acc') -> go (acc ++ acc') (depth + 1)
          (Just res, acc') -> (Just res, acc ++ acc') 

    -- The main proof search loop
    loop :: Prover s ()
    loop =
      -- Find a goal node
      popGoal >>= \case
        Nothing ->
          -- If there are no further goals, check global correctness condition.
          isGloballyCorrect
        Just (node, clause) -> do
          let (unorientated, res) = simplifyClause clause

          unless (null unorientated) $ do
            tell unorientated

          case res of
            Refl ->
              -- Reflexivity or absurd hypotheses
              pure ()
            Absurd clause' -> do
              -- Consequent of goal is absurd

              node' <- insertNode (clause' {clauseGoal = Nothing})
              insertEdge node node' (Proof.identityEdge (clauseVars clause') "")
            Cong clauses -> do
              -- Congruence of constructors

              forM_ clauses $ \clause' -> do
                node' <- insertNode clause'
                insertEdge node node' (Proof.identityEdge (clauseVars clause') "")
            FunEx argTy k -> do
              -- Apply function extensionality

              x <- freshVar argTy
              node' <- insertNode (k x)
              insertEdge node node' (Proof.identityEdge (clauseVars clause) "")
            Reduce clause' -> do
              -- Make a reduction step

              node' <- insertNode clause'
              insertEdge node node' (Proof.identityEdge (clauseVars clause') "")
            Stuck clause' -> do
              decreaseFuel

              chooseM
                [ caseStep node clause',
                  substStep node clause',
                  refuteStep node clause'
                ]
          loop

    substStep, caseStep, refuteStep :: Int -> Clause -> Prover s ()
    -- Substitute a sub-expression
    substStep node clause = do
      -- Choose a lemma clause
      (lemmaNode, lemmaClause) <- gets proverLemmas >>= choose
      (tyTheta, theta, lemmaClause') <- freshenClause lemmaClause

      -- Rewrite goal clause
      let ?hypotheses = clauseHypRules clause
      (theta', maybeCont) <- superpose clause lemmaClause'

      -- Insert edge to lemma
      let edge = Proof.substEdge (clauseVars clause) (theta `composeSubst` theta')
      insertEdge node lemmaNode edge

      case maybeCont of
        Nothing -> pure ()
        Just continuation -> do
          -- Add continuation node
          node' <- insertNode continuation
          insertEdge node node' (Proof.identityEdge (clauseVars clause) "")

    -- Perform case analysis
    caseStep node clause = do
      -- Make node a lemma.
      markNodeAsLemma node

      -- Choose a critical expression
      subject <- choose (clauseCriticals clause)

      case exprType subject of
        DataTy dataType tyArgs -> do
          cases <- casesOf dataType tyArgs
          forM_ cases $ \(k, xs) -> do
            -- The expression indicating the case of the subject.
            let result = mkApps (Con k tyArgs) [Var x [] | x <- xs]

            -- Construct the new clause.
            clause' <-
              if ?conditional
                then do
                  -- Case analysis extends hypothese in conditional mode.
                  pure
                    clause
                      { clauseVars = xs ++ clauseVars clause,
                        clauseHypEqs = mkEquation subject result : clauseHypEqs clause
                      }
                else do
                  -- In normal mode, case analysis must be performed on a variable.
                  Var x [] <- pure subject
                  pure
                    clause
                      { clauseVars = xs ++ clauseVars clause,
                        clauseGoal = substEquation Map.empty (Map.singleton x result) <$> clauseGoal clause
                      }

            -- Insert case into proof
            node' <- insertNode clause'
            insertEdge node node' (Proof.caseEdge (clauseVars clause) subject result xs)
        nonDataType -> empty

    -- Switch to refutation mode
    refuteStep node clause
      | not ?conditional = empty
      | null (clauseHypEqs clause),
        null (clauseHypRules clause) =
          empty -- Empty hypotheses are always satisfiable.
      | Just _ <- clauseGoal clause = do
          node' <- insertNode (clause {clauseGoal = Nothing})
          insertEdge node node' (Proof.identityEdge (clauseVars clause) "")
      | otherwise =
          empty -- Clause is already in refutation mode

-- * Lemmas and Subst

-- | Rewrite the first clause with an instance of the second.
superpose ::
  forall s.
  ( ?program :: Program,
    ?hypotheses :: Hypotheses
  ) =>
  Clause ->
  Clause ->
  Prover
    s
    ( Subst,
      Maybe Clause
    )
superpose
  clause
  lemmaClause@Clause
    { clauseVars = lemmaVars,
      clauseTyVars = lemmaTyVars,
      clauseHypRules = lemmaHypRules,
      clauseHypEqs = lemmaHypEqs,
      clauseGoal = Nothing
    } = do
    -- Attempt to solve hypotheses
    (tyTheta, theta) <- solveEquations lemmaTyVars lemmaVars (lemmaHypRules ++ lemmaHypEqs) Map.empty Map.empty
    pure
      ( theta,
        Nothing
      )
superpose
  clause@Clause {clauseGoal = Just (Equation _ lhs rhs)}
  lemmaClause@Clause
    { clauseVars = lemmaVars,
      clauseTyVars = lemmaTyVars,
      clauseHypRules = lemmaHypRules,
      clauseHypEqs = lemmaHypEqs,
      clauseGoal = Just (Equation _ lemmaLhs lemmaRhs)
    } = do
    chooseM
      [ go lhs rhs lemmaLhs lemmaRhs,
        go lhs rhs lemmaRhs lemmaLhs,
        go rhs lhs lemmaLhs lemmaRhs,
        go rhs lhs lemmaRhs lemmaLhs
      ]
    where
      lemmaHyps :: [Equation]
      lemmaHyps =
        lemmaHypRules
          ++ lemmaHypEqs

      go ::
        Expr -> -- C[s\theta]
        Expr -> -- r
        Expr -> -- s
        Expr -> -- t
        Prover
          s
          ( Subst,
            Maybe Clause -- C[t\theta] = r
          )
      go lhs rhs patLhs patRhs = do
        -- Choose a non-variable sub-expression of lhs
        (subExpr, ctx) <- choose (subExprs lhs)
        guard $ case subExpr of Var _ _ -> False; noNVar -> True

        -- Match with lemma with sub-expression
        (tyTheta, theta) <- choose (matchExpr lemmaTyVars lemmaVars patLhs subExpr)

        -- Instantiate lemma's hypotheses and simplify
        case simplifyEquations
          ( fmap (substEquation tyTheta theta) lemmaHyps
          ) of
          Nothing -> empty
          Just lemmaHyps' -> do
            -- Solve hypotheses over remaining variables
            (tyTheta', theta') <- solveEquations lemmaTyVars lemmaVars lemmaHyps' tyTheta theta

            -- Apply substitution to right-hand side.
            let resExpr = substExpr tyTheta' theta' patRhs

            pure
              ( theta',
                Just
                  clause
                    { -- Existential variables become universal, we assume all types are inhabited.
                      clauseTyVars = (lemmaTyVars List.\\ Map.keys tyTheta') ++ clauseTyVars clause,
                      clauseVars = (lemmaVars List.\\ Map.keys theta') ++ clauseVars clause,
                      clauseGoal = Just (mkEquation (closeContext resExpr ctx) rhs)
                    }
              )
superpose _ _ = empty

-- * Case analysis

-- | Generate a fresh instance for each possible constructor.
casesOf :: (?dataTypeEnv :: DataTypeEnv) => DataType -> [Type] -> Prover s [(DataCon, [Var])]
casesOf dataType tyArgs =
  case Map.lookup dataType ?dataTypeEnv of
    Nothing -> error "Could not find datatype!"
    Just cons ->
      forM cons $ \con -> do
        xs <- mapM freshVar (dataConInstArgTys con tyArgs)
        pure (con, xs)

-- * Utilities

-- | The monad for proof search.
newtype Prover s a = Prover
  { unProver ::
      StateT -- Prover State
        ProverState
        ( LogicT -- Non-determinism
            ( WriterT
                [Equation] -- Unoriented equations
                (FreshM s) -- Fresh name generation
            )
        )
        a
  }
  deriving newtype
    ( Functor,
      Applicative,
      Alternative,
      Monad,
      MonadPlus,
      MonadLogic,
      MonadFresh,
      MonadState ProverState
    )

instance MonadFail (Prover s) where
  fail _ = empty

instance MonadWriter [Equation] (Prover s) where
  tell es = Prover $ lift $ lift $ tell es

-- | Perform proof search.
runProver :: (forall s. Prover s ()) -> ProverState -> (Maybe ProverState, [Equation])
runProver prover st =
  runFreshM $
    runWriterT $
      unLogicT
        (execStateT (unProver prover) st)
        (\st _ -> pure (Just st))
        (pure Nothing)

-- | Proof search state.
data ProverState = ProverState
  { -- | The remaining fuel.
    proverFuel :: !Int,
    -- | A partial proof satisfying the global correctness condition.
    proverProof :: !Proof.Proof,
    -- | A collection of nodes that can be used as lemmas.
    proverLemmas :: [(Int, Clause)],
    -- | Unjustified nodes in the proof.
    proverGoals :: Seq.Seq (Int, Clause),
    -- | Sucess percentage of clause simplification.
    proverStats :: [Int]
  }

-- | Initialise prover state.
initProver :: Int -> [Clause] -> [Clause] -> ProverState
initProver fuel lemmas goals =
  let (proof, nodes) =
        List.mapAccumL
          ( \proof clause ->
              let (proof', node) = Proof.insertNode clause proof
               in (proof', (node, clause))
          )
          Proof.empty
          (lemmas ++ goals)
      (lemmaNodes, goalNodes) = splitAt (length lemmas) nodes
   in ProverState
        { proverFuel = fuel,
          proverProof = proof,
          proverLemmas = lemmaNodes,
          proverGoals = Seq.fromList goalNodes,
          proverStats = []
        }

-- | Decrease the state's fuel.
decreaseFuel :: Prover s ()
decreaseFuel = do
  st <- get
  guard (proverFuel st > 0)
  put st {proverFuel = proverFuel st - 1}

-- | Find the next unjustified node to expand.
popGoal :: Prover s (Maybe (Int, Clause))
popGoal = do
  st <- get
  case proverGoals st of
    Seq.Empty -> pure Nothing
    goals Seq.:|> goal -> do
      put st {proverGoals = goals}
      pure (Just goal)

-- | Check the globabl correctness condition.
isGloballyCorrect :: (?online :: Bool) => Prover s ()
isGloballyCorrect = do
  st <- get
  case Proof.closure (proverProof st) of
    Nothing -> empty
    Just proof ->
      put st {proverProof = proof}

-- | Insert a clause into a the proof graph as a new node.
insertNode :: Clause -> Prover s Int
insertNode clause = do
  st <- get
  let (proof, node) = Proof.insertNode clause (proverProof st)
  put
    st
      { proverProof = proof,
        proverGoals = (node, clause) Seq.:<| proverGoals st
      }
  pure node

-- | Insert edge into proof graph.
insertEdge :: (?online :: Bool) => Int -> Int -> Proof.Edge -> Prover s ()
insertEdge source target edge = do
  st <- get
  case Proof.insertEdge source target edge (proverProof st) of
    Nothing -> empty
    Just proof ->
      put st {proverProof = proof}

-- | Indicate the a node can be used with Subst.
markNodeAsLemma :: Int -> Prover s ()
markNodeAsLemma node = do
  modify $ \st ->
    let clause = Proof.lookupNode node (proverProof st)
     in st {proverLemmas = (node, clause) : proverLemmas st}

-- | Fair choice.
choose :: Foldable f => f a -> Prover s a
choose =
  foldr ((<|>) . pure) empty
{-# INLINE choose #-}

-- | Fair choice.
chooseM :: Foldable f => f (Prover s a) -> Prover s a
chooseM =
  foldr (<|>) empty
{-# INLINE chooseM #-}
