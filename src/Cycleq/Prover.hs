{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingVia #-}

module Cycleq.Prover where

import Cycleq.Environment
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Cycleq.Edge
import Cycleq.Equation
import Cycleq.Proof
import Cycleq.Reduction
import qualified Data.List as List
import GHC.Core.TyCo.Rep
import GHC.Plugins hiding (empty)

-- | Breadth-first search for a proof.
prover ::
  Equation ->
  ReaderT ProgramEnv CoreM (Maybe Proof)
prover equation = do
  let proof = initProof [] [equation] 
  go [(10, proof)]
  where
    go [] = pure Nothing
    go ((fuel, proof) : proofs)
      | fuel <= 0 = go proofs
      | otherwise = do
        proofs' <- mapReaderT (runNonDetCoreM . flip execStateT proof) step
        case List.find (null . proofIncompleteNodes) proofs' of
          Nothing -> go (proofs ++ fmap (fuel - 1,) proofs')
          Just proof' -> pure (Just proof')

type ProverM env = ReaderT env (StateT Proof NonDetCoreM)

cut :: [ProverM env a] -> ProverM env a
cut ms = ReaderT $ \r ->
  StateT $ \s -> 
    firstSuccess $ fmap (\m -> runStateT (runReaderT m r) s) ms

-- | Expand a partial proof tree.
step :: ProverM ProgramEnv ()
step = do
  proof <- get
  case proofIncompleteNodes proof of
    [] -> pure ()
    (node : _) -> do
      equation@(Equation ys lhs rhs) <- lookupNode node
      markNodeAsJustified node
      pprTraceM (show node ++ ":") (ppr equation)

      reduceEquation equation >>= \case
        Left equation' -> do
          -- Reduce
          node' <- insertNode equation'
          insertEdge (identityEdge equation equation') node node'

          pprTraceM "Reduct:" (ppr [node'])
          step
        Right stuckOn ->
          cut
            [ do
                -- Reflexivity
                refl equation

                pprTraceM "Refl:" (ppr ([] :: [Node]))
                step,
              do
                -- Congruence
                equations' <- consCong equation
                nodes <-
                  mapM
                    ( \equation' -> do
                        node' <- insertNode equation'
                        insertEdge (identityEdge equation equation') node node'
                        pure node'
                    )
                    equations'
                pprTraceM "Cong:" (ppr nodes)
                step,
              do
                -- Function Extensionality
                markNodeAsLemma node
                equation' <- funExt equation
                node' <- insertNode equation'
                insertEdge (identityEdge equation equation') node node'

                pprTraceM "FunExt:" (ppr [node'])
                step,

              do
                -- Superposition
                -- Select a lemma node
                node' <- gets proofLemmas >>= msum . fmap pure
                equation' <- lookupNode node'

                -- Rewrite current goal
                (subst, equation'') <- superpose equation equation'
                node'' <- insertNode equation''

                -- Add edges
                insertEdge (identityEdge equation equation'') node node''
                insertEdge (substEdge subst equation equation') node node'

                pprTraceM "Super:" (ppr [node', node''])
              <|>
              do
                -- Case analysis
                markNodeAsLemma node
                case stuckOn of
                  Nothing -> empty
                  Just x
                    | TyConApp dty tyargs <- idType x -> do
                      nodes' <-
                        casesOf dty tyargs
                          >>= mapM
                            ( \(k, xs) -> do
                                scope <- withReaderT (intoEquationEnv ys) (asks envInScopeSet)
                                -- ReductionEnv {reductionInScopeSet} <- asks (mkReductionEnv (equationVars equation))
                                let subst = mkOpenSubst scope [(x, mkConApp2 k tyargs xs)]
                                    equation' =
                                      Equation 
                                        (xs ++ (x `List.delete` ys))
                                        (substExpr subst lhs)
                                        (substExpr subst rhs)
                                node' <- insertNode equation'
                                insertEdge (caseEdge x xs equation equation') node node'
                                pure node'
                            )

                      pprTraceM "Case:" (ppr nodes')
                    | otherwise -> empty
            ]

-- | Try to reduce either side of an equation.
reduceEquation :: Equation -> ProverM ProgramEnv (Either Equation (Maybe Id))
reduceEquation (Equation xs lhs rhs) = withReaderT (intoEquationEnv xs) $ do
  lhs <- reduce lhs
  rhs <- reduce rhs
  pure $
    if reductIsProper lhs || reductIsProper rhs
      then Left (Equation xs (reductExpr lhs) (reductExpr rhs))
      else Right (reductStuckOn lhs <|> reductStuckOn rhs)

-- | Reflexivity
refl :: Equation -> ProverM ProgramEnv ()
refl (Equation xs lhs rhs) = do
  scope <- asks (envInScopeSet . intoEquationEnv xs)
  guard (eqExpr scope lhs rhs)

-- | Decompose an equation by congruence if both sides are headed by a constructor or literal.
consCong :: Equation -> ProverM env [Equation]
consCong (Equation xs (ConApp con (filter isValArg -> args)) (ConApp con' (filter isValArg -> args')))
  | con == con' = pure (zipWith (\arg arg' -> Equation xs arg arg') args args')
consCong (Equation _ (Lit' lit) (Lit' lit'))
  | lit == lit' = pure []
consCong _ = empty

-- | Create a fresh variable as an argument to both sides.
funExt :: Equation -> ProverM env Equation
funExt (Equation xs lhs rhs) = do
  let ty = exprType lhs
  guard (isFunTy ty)
  x <- freshVar (funArgTy ty)
  pure
    $ Equation (x : xs) (App lhs (Var x)) (App rhs (Var x))


-- | Generate a fresh instance for each possible constructor.
casesOf :: TyCon -> [Type] -> ProverM env [(DataCon, [Var])]
casesOf dty tyargs =
  mapM (\con -> (con,) <$> mapM freshVar (scaledThing <$> dataConInstArgTys con tyargs)) (tyConDataCons dty)

-- | Create a fresh variable of a given type.
freshVar :: Type -> ProverM env Id
freshVar ty = do
  unique <- lift $ lift getUniqueM
  let name = mkInternalName unique (mkVarOcc ("x_" ++ show unique)) (UnhelpfulSpan UnhelpfulGenerated)
  pure (mkLocalId name Many ty)

-- | Rewrite the first equation with an instance of the second.
superpose :: Equation -> Equation -> ProverM ProgramEnv (Subst, Equation)
superpose goal@(Equation xs _ _) lemma@(Equation ys lhs rhs) = do
  scope <- withReaderT (intoEquationEnv xs) (asks envInScopeSet)
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
