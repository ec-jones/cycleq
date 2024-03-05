module CycleQ.Reduction
  ( reduce,
    reduceWithCriticals,
  )
where

import CycleQ.Syntax
import Data.Foldable
import Data.Map qualified as Map
import Data.Set qualified as Set

-- | Reduce an expression.
reduce ::
  ( ?program :: Program,
    ?hypotheses :: Hypotheses
  ) =>
  Expr ->
  Expr
reduce expr =
  let (_, _, expr') = reduceWithCriticals expr
   in expr'
{-# INLINE reduce #-}

-- | Reduce an expression with critical expression analysis.
reduceWithCriticals ::
  ( ?program :: Program,
    ?hypotheses :: Hypotheses
  ) =>
  Expr ->
  ( Bool, -- \^ At least one reduction step?
    Set.Set Expr, -- \^ Critical expressions needed for further reduction.
    Expr -- \^ Reduct
  )
reduceWithCriticals expr =
  let (p, reduct) = reduceWithCriticals' expr []
   in (p, getCriticals reduct, getExpr reduct)
{-# INLINE reduceWithCriticals #-}

reduceWithCriticals' ::
  ( ?program :: Program,
    ?hypotheses :: Hypotheses
  ) =>
  Expr ->
  [Reduct] ->
  (Bool, Reduct)
reduceWithCriticals' (Var x tyArgs) args
  -- Apply hypotheses
  | (True, reduct) <- applyHypotheses ?hypotheses expr =
      (True, mkReduct reduct) -- Hypothese are assumed to be already be irreducible.

  -- Unfold program definitions
  | Just (as, defn) <- lookupProgram x ?program = do
      let tyTheta = Map.fromList (zip as tyArgs)

      case reduceDefn tyTheta defn args of
        Left criticals ->
          (False, Reduct expr criticals)
        Right (body, args')
          | exprType expr /= exprType body ->
              error ("Type reduction error: " ++ show (expr, tyTheta, body))
          | otherwise ->
              let (_, reduct) = reduceWithCriticals' body args'
               in (True, reduct)
  | otherwise =
      (False, Reduct expr Set.empty)
  where
    -- The expression to be reduced
    expr :: Expr
    expr = appReduct (Var x tyArgs) args
reduceWithCriticals' (Con con tyArgs) args =
  (False, RConApp con tyArgs args)
reduceWithCriticals' (Lit lit) _ =
  (False, RLit lit)
reduceWithCriticals' (App fun arg) args =
  let (p, arg') = reduceWithCriticals' arg []
      (q, app) = reduceWithCriticals' fun (arg' : args)
   in (p || q, app)

-- | Attempt to reduce a function definition under a series of arguments.
reduceDefn ::
  TySubst -> -- \^ Type instance
  Body -> -- \^Function body
  [Reduct] -> -- \^Arguments
  Either
    (Set.Set Expr) -- \^Critical expressions
    ( Expr, -- \^ Reduct
      [Reduct] -- \^ Remaining arguments
    )
reduceDefn tyTheta = go Map.empty
  where
    go :: Map.Map Var Reduct -> Body -> [Reduct] -> Either (Set.Set Expr) (Expr, [Reduct])
    go theta (Lam x body) [] =
      Left Set.empty -- Insufficient arguments
    go theta (Lam x body) (arg : args) =
      go (Map.insert x arg theta) body args
    go theta (Case x alts) args =
      case Map.lookup x theta of
        Nothing ->
          let subject = Var x []
           in Left (Set.singleton subject)
        Just (RConApp con tyArgs conArgs) ->
          let (xs, rhs) = lookupConAlt con alts
              theta' = Map.fromList (zip xs conArgs) <> theta
           in go theta' rhs args
        Just (RLit lit) ->
          let rhs = lookupLitAlt lit alts
           in go theta rhs args
        Just (Reduct subject criticals) ->
          Left (Set.insert subject criticals)
    go theta (Body body) args =
      Right
        ( substExpr tyTheta (fmap getExpr theta) body,
          args
        )
    go theta Bottom args =
      error "Impossible branch reached!"

-- | Find the case alternative associated with the given constructor.
lookupConAlt :: DataCon -> [Alt] -> ([Var], Body)
lookupConAlt con [] = error "Incomplete case expression!"
lookupConAlt con altss@(alt : alts) =
  case alt of
    Default rhs -> go alts (Just rhs)
    nonDefault -> go altss Nothing
  where
    go :: [Alt] -> Maybe Body -> ([Var], Body)
    go [] Nothing = error "Incomplete case expression!"
    go [] (Just rhs) = ([], rhs)
    go (Default rhs : _) def = error "Double default!"
    go (ConAlt con' xs rhs : alts) def
      | con == con' = (xs, rhs)
      | otherwise = go alts def
    go (LitAlt _ _ : alts) def = go alts def

-- | Find the case alternative associated with the given literal.
lookupLitAlt :: Literal -> [Alt] -> Body
lookupLitAlt lit [] = error "Incomplete case expression!"
lookupLitAlt lit altss@(alt : alts) =
  case alt of
    Default rhs -> go alts (Just rhs)
    nonDefault -> go altss Nothing
  where
    go :: [Alt] -> Maybe Body -> Body
    go [] Nothing = error "Incomplete case expression!"
    go [] (Just rhs) = rhs
    go (Default rhs : _) def = error "Double default!"
    go (ConAlt _ _ _ : alts) def = go alts def
    go (LitAlt lit' rhs : alts) def
      | lit == lit' = rhs
      | otherwise = go alts def

-- * Reducts

-- | The result of attempting to reduce an expression.
data Reduct
  = Reduct
      !Expr
      (Set.Set Expr) -- \^ Critical sub-expressions
  | RConApp
      !DataCon
      [Type]
      [Reduct]
  | RLit !Literal

mkReduct :: Expr -> Reduct
mkReduct expr =
  case viewConApp expr of
    Nothing -> Reduct expr Set.empty
    Just (con, tyArgs, conArgs) ->
      RConApp con tyArgs (fmap mkReduct conArgs)

getExpr :: Reduct -> Expr
getExpr (Reduct expr _) = expr
getExpr (RConApp con tyArgs conArgs) =
  appReduct (Con con tyArgs) conArgs
getExpr (RLit lit) = Lit lit
{-# INLINE getExpr #-}

getCriticals :: Reduct -> Set.Set Expr
getCriticals (Reduct _ criticals) = criticals
getCriticals (RConApp _ _ _) = Set.empty
getCriticals (RLit _) = Set.empty
{-# INLINE getCriticals #-}

appReduct :: Expr -> [Reduct] -> Expr
appReduct = foldl' (\hd -> App hd . getExpr)
{-# INLINE appReduct #-}
