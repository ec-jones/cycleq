{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Cycleq.Prover where

import Cycleq.Patterns
import Control.Applicative
import Control.Monad
import Control.Monad.Freer
import Control.Monad.Freer.NonDet
import Control.Monad.Freer.Reader
import Control.Monad.Freer.State
import Cycleq.Edge
import Cycleq.Equation
import Cycleq.Proof
import Cycleq.Reduction
import qualified Data.List as List
import GHC.Core.TyCo.Rep
import GHC.Plugins hiding (empty)

-- | Breadth-first search for a proof.
prover ::
  ( Member CoreM es,
    Member (Reader Context) es
  ) =>
  Equation ->
  Eff es (Maybe Proof)
prover equation = do
  proof <- execState (emptyProof []) (insertNode equation)
  go [(10, proof)]
  where
    go [] = pure Nothing
    go ((fuel, proof) : proofs)
      | fuel <= 0 = go proofs
      | otherwise = do
        proofs' <- makeChoiceA (execState proof step)
        case List.find (null . proofIncompleteNodes) proofs' of
          Nothing -> go (proofs ++ fmap (fuel - 1,) proofs')
          Just proof' -> pure (Just proof')

-- | Expand a partial proof tree.
step ::
  ( Member CoreM es,
    Member (Reader Context) es,
    Member NonDet es,
    Member (State Proof) es
  ) =>
  Eff es ()
step = do
  nodes <- gets proofIncompleteNodes
  case nodes of
    [] -> pure ()
    (node : _) -> do
      equation <- lookupNode node
      send $ putMsg (ppr node GHC.Plugins.<> text ":" <+> ppr equation)
      local
        (extendContextFreeVars (equationVars equation))
        (reduceEquation equation)
        >>= \case
          Left equation' -> do
            node' <- insertNode equation'
            insertEdge (identityEdge equation equation') node node'

            send (putMsg $ text "Reduct: " <+> ppr [node'])
            markNodeAsComplete node
            step
          Right mx ->
            msum
              [ -- Refl
                do
                  local
                    (extendContextFreeVars (equationVars equation))
                    (refl equation)

                  send (putMsg $ text "Refl: []")
                  markNodeAsComplete node
                  step,
                -- Cong
                do
                  equations' <- consCong equation
                  nodes' <-
                    mapM
                      ( \equation' -> do
                          node' <- insertNode equation'
                          insertEdge (identityEdge equation equation') node node'
                          pure node'
                      )
                      equations'

                  send (putMsg $ text "Cong: " <+> ppr nodes')
                  markNodeAsComplete node
                  step,
                -- FunExt
                do
                  equation' <- funExt equation
                  node' <- insertNode equation'
                  insertEdge (identityEdge equation equation') node node'

                  send (putMsg $ text "FunExt: " <+> ppr [node'])
                  markNodeAsComplete node
                  step,
                -- Super
                do
                  -- Select a lemma node
                  node' <- gets proofLemmas >>= choose
                  equation' <- lookupNode node'

                  -- Rewrite current goal
                  (subst, equation'') <- superpose equation equation'
                  node'' <- insertNode equation''

                  -- Add edges
                  insertEdge (identityEdge equation equation'') node node''
                  insertEdge (substEdge subst equation equation') node node'

                  send (putMsg $ text "Super: " <+> ppr [node', node''])
                  markNodeAsComplete node,
                -- Case
                case mx of
                  Nothing -> empty
                  Just x
                    | TyConApp dty tyargs <- idType x -> do
                      nodes' <-
                        casesOf dty tyargs
                          >>= mapM
                            ( \(k, xs) -> do
                                Context {contextInScopeSet} <- asks (extendContextFreeVars (equationVars equation))
                                let subst = mkOpenSubst contextInScopeSet [(x, mkConApp2 k tyargs xs)]
                                    equation' =
                                      substEquation
                                        subst
                                        equation
                                          { equationVars = xs ++ (x `List.delete` equationVars equation)
                                          }
                                node' <- insertNode equation'
                                insertEdge (caseEdge x xs equation equation') node node'
                                pure node'
                            )

                      send (putMsg $ text "Case: " <+> ppr nodes')
                      markNodeAsComplete node
                      markNodeAsSuper node
                    | otherwise -> empty
              ]

-- | Try to reduce either side of an equation.
reduceEquation :: (Member (Reader Context) es) => Equation -> Eff es (Either Equation (Maybe Id))
reduceEquation eq@Equation {equationLeft, equationRight} = do
  lhs <- reduce equationLeft
  rhs <- reduce equationRight
  pure $
    if reductIsProper lhs || reductIsProper rhs
      then Left (eq {equationLeft = reductExpr lhs, equationRight = reductExpr rhs})
      else Right (reductStuck lhs <|> reductStuck rhs)

-- | Reflexivity
refl :: (Member (Reader Context) es, Member NonDet es) => Equation -> Eff es ()
refl Equation {equationLeft, equationRight} = do
  Context {contextInScopeSet} <- ask
  guard (eqExpr contextInScopeSet equationLeft equationRight)

-- | Decompose an equation by congruence if both sides are headed by a constructor or literal.
consCong :: Member NonDet es => Equation -> Eff es [Equation]
consCong eq@Equation {equationLeft = ConApp con (filter isValArg -> args), equationRight = ConApp con' (filter isValArg -> args')}
  | con == con' = pure (zipWith (\arg arg' -> eq {equationLeft = arg, equationRight = arg'}) args args')
consCong eq@Equation {equationLeft = Lit' lit, equationRight = Lit' lit'}
  | lit == lit' = pure []
consCong _ = empty

-- | Create a fresh variable as an argument to both sides.
funExt :: (Member NonDet es, Member CoreM es) => Equation -> Eff es Equation
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
casesOf :: Member CoreM es => TyCon -> [Type] -> Eff es [(DataCon, [Var])]
casesOf dty tyargs =
  mapM (\con -> (con,) <$> mapM freshVar (scaledThing <$> dataConInstArgTys con tyargs)) (tyConDataCons dty)

-- | Create a fresh variable of a given type.
freshVar :: Member CoreM es => Type -> Eff es Id
freshVar ty = do
  unique <- send (getUniqueM :: CoreM Unique)
  let name = mkInternalName unique (mkVarOcc ("x_" ++ show unique)) (UnhelpfulSpan UnhelpfulGenerated)
  pure (mkLocalId name Many ty)

-- | Rewrite the first equation with an instance of the second.
superpose :: (Member (Reader Context) es, Member NonDet es, Member CoreM es) => Equation -> Equation -> Eff es (Subst, Equation)
superpose goal lemma@Equation {equationVars, equationLeft, equationRight} = do
  Context {contextInScopeSet} <- asks (extendContextFreeVars equationVars)
  (expr, ctx) <- choose (equationSubtermsForSuper goal)
  ( do
      guard (isNonVar equationLeft)
      subst <- match equationVars contextInScopeSet equationLeft expr
      pure (subst, ctx (substExpr subst equationRight))
    )
    <|> ( do
            guard (isNonVar equationRight)
            subst <- match equationVars contextInScopeSet equationRight expr
            pure (subst, ctx (substExpr subst equationLeft))
        )
  where
    isNonVar (Var _) = False
    isNonVar _ = True

-- | Find an instance of the first expression that is alpha equivalent to the second.
match :: forall es. Member NonDet es => [Id] -> InScopeSet -> CoreExpr -> CoreExpr -> Eff es Subst
match univs scope expr1 expr2 = do
  guard (eqType (exprType expr1) (exprType expr2))
  runReader (mkRnEnv2 scope) $ execState (mkEmptySubst scope) (go expr1 expr2)
  where
    go :: CoreExpr -> CoreExpr -> Eff (State Subst ': Reader RnEnv2 ': es) ()
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

infixr 2 `cut`

-- | Take only the first element if it succeeds.
cut :: Member NonDet es => Eff es a -> Eff es a -> Eff es a
cut m1 m2 =
  msplit m1 >>= \case
    Nothing -> m2
    Just (a, m1') -> pure a

-- | Choose an element from a list.
choose :: Member NonDet es => [a] -> Eff es a
choose = msum . fmap pure
