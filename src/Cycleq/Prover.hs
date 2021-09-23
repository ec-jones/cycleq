{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Cycleq.Prover 
  ( prover
  )
  where

import Control.Applicative
import Control.Monad
import Control.Monad.Logic
import Control.Monad.Reader
import Control.Monad.State
import Cycleq.Edge
import Cycleq.Equation
import Cycleq.Proof
import Cycleq.Reduction
import qualified Data.List as List
import qualified Data.IntMap as IntMap
import GHC.Core.TyCo.Rep
import GHC.Plugins hiding (empty)

newtype Prover env a = Prover
  { unProver ::ReaderT env (LogicT CoreM) a
  }
  deriving newtype
    ( Functor,
      Applicative,
      Alternative,
      Monad,
      MonadPlus,
      MonadLogic,
      MonadReader env
    ) 

instance MonadUnique (Prover env) where
  getUniqueSupplyM = Prover $ lift $ lift getUniqueSupplyM

localEquationEnv :: [Id] -> Prover EquationEnv a -> Prover ProgramEnv a
localEquationEnv xs m = Prover $ withReaderT (mkEquationEnv xs) . unProver m

execProver :: Prover env a -> ReaderT env CoreM [Proof]
execProver m = mapReaderT observeAllT . execStateT (unProver m)

proverTrace :: SDoc -> Prover env ()
proverTrace sdoc = Prover $ lift $ lift $ putMsg sdoc

-- | Breadth-first search for a proof.
prover ::
  [Equation] ->
  Equation ->
  ReaderT ProgramEnv CoreM (Maybe Proof)
prover lemmas equation = do
  proof <- execStateT (insertNode equation) (emptyProof lemmas)
  go [(10, proof)]
  where
    go [] = pure Nothing
    go ((fuel, proof) : proofs)
      | fuel <= 0 = go proofs
      | otherwise = do
        proofs' <- execProver step proof
        -- mapM_ (\proof' -> 
        --     lift $ putMsg $ ppr (IntMap.lookup 4 (proofEdges proof') >>= IntMap.lookup 6)
        --   )
        --   proofs'
        case List.find (null . proofIncompleteNodes) proofs' of
          Nothing -> go (proofs ++ fmap (fuel - 1,) proofs')
          Just proof' -> do
            pure (Just proof')

-- | Expand a partial proof tree.
step :: Proof -> Prover ProgramEnv Proof
step proof = do
  nodes <- gets proofIncompleteNodes
  case nodes of
    [] -> pure ()
    (node : _) -> do
      equation@Equation {equationVars} <- lookupNode node
      proverTrace (ppr node GHC.Plugins.<> text ":" <+> ppr equation)
      reduceEquation equation
        >>= \case
          Left equation' -> do
            node' <- insertNode equation'
            insertEdge (identityEdge equation equation') node node'

            proverTrace (text "Reduct: " <+> ppr [node'])
            markNodeAsComplete node
            step
          Right mx ->
            onceFrom
                [ do
                    -- Refl
                    refl equation

                    proverTrace (text "Refl: []")
                    markNodeAsComplete node
                    step,
                  do
                    -- Cong
                    nodes' <- 
                      consCong equation >>= 
                        mapM
                          ( \equation' -> do
                              node' <- insertNode equation'
                              insertEdge (identityEdge equation equation') node node'
                              pure node'
                          )

                    proverTrace (text "Cong: " <+> ppr nodes')
                    markNodeAsComplete node
                    step,
                  do
                    -- FunExt
                    equation' <- funExt equation
                    node' <- insertNode equation'
                    insertEdge (identityEdge equation equation') node node'

                    proverTrace (text "FunExt: " <+> ppr [node'])
                    markNodeAsSuper node
                    markNodeAsComplete node
                    step
                ]
              `interleave`
                do
                  -- Super
                  -- Select a lemma node
                  node' <- gets proofLemmas >>= choose
                  equation' <- lookupNode node'

                  -- Rewrite current goal
                  (subst, equation'') <- superpose equation equation'
                  node'' <- insertNode equation''

                  -- Add edges
                  insertEdge (identityEdge equation equation'') node node''
                  insertEdge (substEdge subst equation equation') node node'

                  proverTrace (text "Super: " <+> ppr [node', node''])
                  markNodeAsComplete node
              `interleave`
                  -- Case
                  case mx of
                    Nothing -> empty
                    Just x
                      | TyConApp dty tyargs <- idType x -> do
                        nodes' <-
                          casesOf dty tyargs
                            >>= mapM
                              ( \(k, xs) -> do
                                  EquationEnv {envInScopeSet} <- asks (mkEquationEnv equationVars)
                                  let subst = mkOpenSubst envInScopeSet [(x, mkConApp2 k tyargs xs)]
                                      equation' =
                                        substEquation
                                          subst
                                          equation
                                            { equationVars = xs ++ (x `List.delete` equationVars)
                                            }
                                  node' <- insertNode equation'
                                  insertEdge (caseEdge x xs equation equation') node node'
                                  pure node'
                              )
                        proverTrace (text "Case: " <+> ppr nodes')
                        markNodeAsSuper node
                        markNodeAsComplete node
                      | otherwise -> empty

-- | Try to reduce either side of an equation.
reduceEquation :: Equation -> Prover ProgramEnv (Either Equation (Maybe Id))
reduceEquation eq@Equation {equationVars, equationLeft, equationRight} = 
  localEquationEnv equationVars $ do
    lhs <- reduce equationLeft
    rhs <- reduce equationRight
    pure $
      if reductIsProper lhs || reductIsProper rhs
        then Left (eq {equationLeft = reductExpr lhs, equationRight = reductExpr rhs})
        else Right (reductStuckOn lhs <|> reductStuckOn rhs)

-- | Reflexivity
refl :: Equation -> Prover ProgramEnv ()
refl Equation {equationVars, equationLeft, equationRight} =
  localEquationEnv equationVars $ do
    EquationEnv {envInScopeSet} <- ask
    guard (eqExpr envInScopeSet equationLeft equationRight)

-- | Decompose an equation by congruence if both sides are headed by a constructor or literal.
consCong :: Equation -> Prover ProgramEnv [Equation]
consCong
  eq@Equation
    { equationLeft = viewConApp -> Just (con, filter isValArg -> args),
      equationRight = viewConApp -> Just (con', filter isValArg -> args')
    }
    | con == con' = pure (zipWith (\arg arg' -> eq {equationLeft = arg, equationRight = arg'}) args args')
consCong
  eq@Equation
    { equationLeft = viewLit -> Just lit,
      equationRight = viewLit -> Just lit'
    }
    | lit == lit' = pure []
consCong _ = empty

-- | Create a fresh variable as an argument to both sides.
funExt :: Equation -> Prover ProgramEnv Equation
funExt Equation {equationVars, equationLeft, equationRight} = do
  let ty = exprType equationLeft
  guard (isFunTy ty)
  x <- freshVar (funArgTy ty)
  pure
    Equation
      { equationVars = x : equationVars,
        equationLeft = App equationLeft (Var x),
        equationRight = App equationRight (Var x)
      }

-- | Generate a fresh instance for each possible constructor.
casesOf :: TyCon -> [Type] -> Prover ProgramEnv [(DataCon, [Var])]
casesOf dty tyargs =
  mapM (\con -> (con,) <$> mapM freshVar (scaledThing <$> dataConInstArgTys con tyargs)) (tyConDataCons dty)

-- | Create a fresh variable of a given type.
freshVar :: Type -> Prover ProgramEnv Id
freshVar ty = do
  unique <- getUniqueM
  let name = mkInternalName unique (mkVarOcc ("x_" ++ show unique)) (UnhelpfulSpan UnhelpfulGenerated)
  pure (mkLocalId name Many ty)

-- | Rewrite the first equation with an instance of the second.
superpose :: Equation -> Equation -> Prover ProgramEnv (Subst, Equation)
superpose goal lemma@Equation {equationVars, equationLeft, equationRight} = 
  localEquationEnv equationVars $ do
    EquationEnv {envInScopeSet} <- ask
    (expr, ctx) <- choose (equationSubtermsForSuper goal)
    ( do
        guard (isNonVar equationLeft)
        subst <- match equationVars envInScopeSet equationLeft expr
        pure (subst, ctx (substExpr subst equationRight))
      )
      `interleave` ( do
              guard (isNonVar equationRight)
              subst <- match equationVars envInScopeSet equationRight expr
              pure (subst, ctx (substExpr subst equationLeft))
          )
  where
    isNonVar (Var _) = False
    isNonVar _ = True

-- | Find an instance of the first expression that is alpha equivalent to the second.
match :: [Id] -> InScopeSet -> CoreExpr -> CoreExpr -> Prover EquationEnv Subst
match univs scope expr1 expr2 = do
  guard (eqType (exprType expr1) (exprType expr2))
  runReaderT (execStateT (go expr1 expr2) (mkEmptySubst scope)) (mkRnEnv2 scope)
  where
    go :: CoreExpr -> CoreExpr -> StateT Subst (ReaderT RnEnv2 (Prover EquationEnv)) ()
    go (Var x) e
      | x `elem` univs = modify (\subst -> extendIdSubst subst x e)
      | Var y <- e = do
        env <- ask
        guard (rnOccL env x == rnOccR env y)
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

choose :: MonadLogic m => [a] -> m a
choose [] = empty
choose (a : as) = 
  pure a `interleave` choose as

onceFrom :: MonadLogic m => [m a] -> m a
onceFrom = once . msum