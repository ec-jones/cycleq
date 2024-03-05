module CycleQ.Syntax.Translation
  ( -- * Translation Monad
    TranslateT,
    translate,
    translateBind,
    translateClause,

    -- * Error Handling
    module Control.Monad.Except,
  )
where

import Control.Monad.Except
import Control.Monad.State
import CycleQ.Syntax
import CycleQ.Unique.Unique
import Data.Bifunctor
import Data.List qualified as List
import Data.Map qualified as Map
import GHC.Builtin.Types.Prim qualified as GHC
import GHC.Core.TyCo.Rep qualified as GHC
import GHC.Plugins qualified as GHC

-- * Interface

-- | The translation monad.
newtype TranslateT m a = TranslateT
  { unTranslate ::
      (DataTypeEnv, Map.Map Var ([TyVar], Body)) ->
      m (Either TranslationError a, (DataTypeEnv, Map.Map Var ([TyVar], Body)))
  }
  deriving
    ( Functor,
      Applicative,
      Monad,
      MonadError TranslationError,
      MonadState (DataTypeEnv, Map.Map Var ([TyVar], Body))
    )
    via ExceptT TranslationError (StateT (DataTypeEnv, Map.Map Var ([TyVar], Body)) m)

instance MonadTrans TranslateT where
  lift go = TranslateT $ \prog -> do
    res <- go
    pure (Right res, prog)

instance GHC.MonadUnique m => GHC.MonadUnique (TranslateT m) where
  getUniqueSupplyM = lift GHC.getUniqueSupplyM

-- | Run a translation.
translate :: Monad m => TranslateT m a -> m (DataTypeEnv, Program, a)
translate go =
  unTranslate go (Map.empty, Map.empty) >>= \case
    (Left err, (dataTypeEnv, prog)) ->
      error "Unhandled error!"
    (Right a, (dataTypeEnv, prog)) ->
      pure (dataTypeEnv, mkProgram prog, a)

-- | Translate a top-level bind.
translateBind ::
  ( GHC.MonadUnique m,
    ?freeVars :: [GHC.Var],
    ?inScopeSet :: GHC.InScopeSet
  ) =>
  GHC.Id ->
  GHC.CoreExpr ->
  TranslateT m ()
translateBind x expr = do
  fun <- translateVar x

  let (as, body) = GHC.collectTyBinders expr
      as' = fmap translateTyVar as

  let ?freeVars = as ++ ?freeVars
      ?inScopeSet = ?inScopeSet `GHC.extendInScopeSetList` as

  body' <- translateBody body
  modify $ second $ Map.insert fun (as', body')

-- | Translate a top-level bind into a clause.
translateClause ::
  (?inScopeSet :: GHC.InScopeSet) =>
  GHC.MonadUnique m =>
  GHC.CoreExpr ->
  TranslateT m Clause
translateClause expr = do
  let (as, xs, body) = GHC.collectTyAndValBinders expr
      as' = fmap translateTyVar as

  xs' <- mapM translateVar xs

  let ?freeVars = as ++ xs
      ?inScopeSet = ?inScopeSet `GHC.extendInScopeSetList` as

  translateExpr body [] []
    >>= exprToClause as' xs'

-- * Types

-- | Translate a type variable.
translateTyVar :: GHC.TyVar -> TyVar
translateTyVar x =
  MkTyVar
    { tyVarUnique = GHC (GHC.getUnique x),
      tyVarName = GHC.occNameString (GHC.occName x)
    }

-- | Translate a monomorphic type.
translateType :: Monad m => GHC.Type -> TranslateT m Type
translateType ty =
  translateType' (GHC.expandTypeSynonyms ty) []

translateType' :: Monad m => GHC.Type -> [Type] -> TranslateT m Type
translateType' (GHC.TyVarTy a) tyArgs =
  pure (TyVar (translateTyVar a) tyArgs)
translateType' (GHC.AppTy ty tyArg) tyArgs = do
  tyArg' <- translateType' tyArg []
  translateType' ty (tyArg' : tyArgs)
translateType' (GHC.TyConApp tyCon tyArgs) _
  -- Function type constructor
  | GHC.isFunTyCon tyCon,
    [] <- tyArgs =
      pure FunTy0
  | GHC.isFunTyCon tyCon,
    [argTy] <- tyArgs =
      FunTy1 <$> translateType argTy
  -- Primitive types
  | tyCon == GHC.charPrimTyCon = pure (LitTy TyLitChar)
  | tyCon == GHC.intPrimTyCon = pure (LitTy TyLitInteger)
  | tyCon == GHC.floatPrimTyCon = pure (LitTy TyLitFloat)
  | tyCon == GHC.doublePrimTyCon = pure (LitTy TyLitDouble)
  | GHC.isPrimTyCon tyCon =
      throwError (UnsupportedPrimitive tyCon)
  -- Newtypes and single method classes.
  | GHC.isNewTyCon tyCon = do
      let (as, ty) = GHC.newTyConRhs tyCon
          as' = fmap translateTyVar as
      tyArgs' <- mapM translateType tyArgs

      -- Unfold the newtype wrapper
      let tyTheta = Map.fromList (zip as' tyArgs')
      substType tyTheta <$> translateType' ty []
  -- Algebraic datatype or class evidence
  | GHC.isVanillaAlgTyCon tyCon || GHC.isClassTyCon tyCon =
      DataTy
        <$> translateDataType tyCon
        <*> mapM (\tyArg -> translateType' tyArg []) tyArgs
  -- Type family or promoted datatype,
  | otherwise =
      throwError (UnsupportedTyCon tyCon)
translateType' (GHC.FunTy _ _ argTy resTy) _ =
  FunTy
    <$> translateType' argTy []
    <*> translateType' resTy []
translateType' ty@(GHC.ForAllTy argTy resTy) tyArgs =
  throwError (HigherRankedType (Just ty))
translateType' (GHC.LitTy _) tyArgs =
  throwError TypeLevelLiteral
translateType' _ _ =
  throwError CastOrCoercion

-- | Translate a polymorphic type.
translatePolyType :: Monad m => GHC.Type -> TranslateT m PolyType
translatePolyType ty = do
  let (as, ty') = GHC.splitForAllTyCoVars (GHC.expandTypeSynonyms ty)
  Forall (fmap translateTyVar as) <$> translateType' ty' []

-- | Translate a datatype.
translateDataType :: Monad m => GHC.TyCon -> TranslateT m DataType
translateDataType dataType = do
  let dataType' =
        MkDataType
          { dataTypeUnique = GHC (GHC.getUnique dataType),
            dataTypeName = GHC.occNameString (GHC.getOccName dataType)
          }

  -- Translate associated constructors
  (dataTypeEnv, prog) <- get
  case Map.lookup dataType' dataTypeEnv of
    Nothing -> do
      -- Mark dataType as seen
      put (Map.insert dataType' [] dataTypeEnv, prog)

      dataCons <- mapM translateDataCon (GHC.tyConDataCons dataType)

      modify $ first $ Map.insert dataType' dataCons
    Just _ -> pure ()

  pure
    MkDataType
      { dataTypeUnique = GHC (GHC.getUnique dataType),
        dataTypeName = GHC.occNameString (GHC.getOccName dataType)
      }

-- | Translate a constructor.
translateDataCon :: Monad m => GHC.DataCon -> TranslateT m DataCon
translateDataCon con = do
  polyTy <- translatePolyType (GHC.dataConRepType con)
  pure
    MkDataCon
      { dataConUnique = GHC (GHC.getUnique con),
        dataConName = GHC.occNameString (GHC.getOccName con),
        dataConType = polyTy
      }

-- * Expressions

-- | Translate a variable.
translateVar :: Monad m => GHC.Id -> TranslateT m Var
translateVar x = do
  polyTy <- translatePolyType (GHC.idType x)
  pure
    MkVar
      { varUnique = GHC (GHC.getUnique x),
        varName = GHC.occNameString (GHC.occName x),
        varType = polyTy
      }

-- | Translate an expression.
translateExpr ::
  ( GHC.MonadUnique m,
    ?freeVars :: [GHC.Var],
    ?inScopeSet :: GHC.InScopeSet
  ) =>
  GHC.CoreExpr ->
  [GHC.Type] ->
  [GHC.CoreExpr] ->
  TranslateT m Expr
translateExpr (GHC.Var x) tyArgs args
  | GHC.ClassOpId cls <- GHC.idDetails x =
      case GHC.idUnfolding x of
        GHC.CoreUnfolding {GHC.uf_tmpl = expr} ->
          translateExpr expr tyArgs args
        noUnfolding ->
          error "Couldn't find class op unfolding!"
  | Just dataCon <- GHC.isDataConWorkId_maybe x =
      mkApps
        <$> (Con <$> translateDataCon dataCon <*> mapM translateType tyArgs)
        <*> mapM (\arg -> translateExpr arg [] []) args
  | otherwise =
      mkApps
        <$> (Var <$> translateVar x <*> mapM translateType tyArgs)
        <*> mapM (\arg -> translateExpr arg [] []) args
translateExpr (GHC.Lit lit) tyArgs _ =
  Lit <$> translateLit lit tyArgs
translateExpr (GHC.App fun arg) tyArgs args
  | GHC.Type tyArg <- arg = do
      translateExpr fun (tyArg : tyArgs) args
  | null tyArgs = do
      translateExpr fun [] (arg : args)
  | otherwise =
      throwError (HigherRankedType Nothing)
translateExpr (GHC.Lam x body) (tyArg : tyArgs) args = do
  -- Beta reduction
  let subst = GHC.mkOpenSubst ?inScopeSet [(x, GHC.Type tyArg)]

  translateExpr (GHC.substExpr subst body) tyArgs args
translateExpr (GHC.Lam x body) [] (arg : args) = do
  -- Beta reduction
  let subst = GHC.mkOpenSubst  ?inScopeSet [(x, arg)]

  translateExpr (GHC.substExpr subst body) [] args
translateExpr expr@GHC.Lam {} [] [] = do
  -- Abstract over local free variables
  let vars = freeVarsFrom (GHC.exprFreeVarsList expr)

  -- Create function body
  fun <- freshLiftVar "lam" vars (GHC.exprType expr)
  translateBind fun (GHC.mkLams vars expr)

  translateExpr (GHC.mkVarApps (GHC.Var fun) vars) [] []
translateExpr expr@GHC.Case {} tyArgs args
  | null tyArgs = do
      -- Abstract over local free variables
      let vars = freeVarsFrom (GHC.exprFreeVarsList expr)

      -- Create function body
      fun <- freshLiftVar "case" vars (GHC.exprType expr)
      translateBind fun (GHC.mkLams vars expr)

      translateExpr (GHC.mkVarApps (GHC.Var fun) vars) [] args
  | otherwise =
      throwError (HigherRankedType Nothing)
translateExpr expr@(GHC.Let (GHC.NonRec x defn) body) tyArgs args = do
  -- Inline non-recursive let.
  let subst = GHC.mkOpenSubst ?inScopeSet [(x, defn)]

  translateExpr (GHC.substExpr subst body) tyArgs args
translateExpr expr@(GHC.Let bind@GHC.Rec {} body) tyArgs args = do
  -- Abstract over local free variables
  let vars = freeVarsFrom (GHC.nonDetEltsUniqSet (GHC.bindFreeVars bind))

  -- Assign variables new identifiers
  bind' <- forM (GHC.flattenBinds [bind]) $ \(x, defn) -> do
    fun <- freshLiftVar (GHC.occNameString (GHC.occName x)) vars (GHC.exprType defn)
    pure (x, fun, defn)

  -- Extend free variables
  let ?freeVars = [fun | (_, fun, _) <- bind'] ++ ?freeVars
      ?inScopeSet = ?inScopeSet `GHC.extendInScopeSetList` [fun | (_, fun, _) <- bind']

  -- Substitute let binders for the new top-level functions
  let subst = GHC.mkOpenSubst ?inScopeSet [(x, GHC.mkVarApps (GHC.Var fun) vars) | (x, fun, _) <- bind']

  -- Emit top-level functions
  forM_ bind' $ \(_, fun, defn) ->
    translateBind fun (GHC.mkLams vars (GHC.substExpr subst defn))

  translateExpr (GHC.substExpr subst body) tyArgs args
translateExpr (GHC.Tick _ expr) tyArgs args =
  -- Ignore ticks
  translateExpr expr tyArgs args
translateExpr expr@(GHC.Cast expr' _) tyArgs args
  -- Newtypes and single method classes are represented with a coercion.
  | Just (tyCon, _) <- GHC.splitTyConApp_maybe (GHC.expandTypeSynonyms (GHC.exprType expr')),
    GHC.isNewTyCon tyCon =
      -- We ignore such coercions, see 'translateType'
      translateExpr expr' tyArgs args
  | Just (tyCon, _) <- GHC.splitTyConApp_maybe (GHC.expandTypeSynonyms (GHC.exprType expr)),
    GHC.isNewTyCon tyCon =
      translateExpr expr' tyArgs args
  | otherwise =
      throwError CastOrCoercion
translateExpr _ _ _ =
  error "Expression is not well-formed!"

-- | Translate a literal.
translateLit :: Monad m => GHC.Literal -> [GHC.Type] -> TranslateT m Literal
-- All other literals are monomorphic
translateLit (GHC.LitChar c) [] = pure (LitChar c)
translateLit (GHC.LitNumber GHC.LitNumInt n) [] = pure (LitInteger n)
translateLit (GHC.LitFloat n) [] = pure (LitFloat n)
translateLit (GHC.LitDouble n) [] = pure (LitDouble n)
translateLit lit _ =
  throwError (UnsupportedLiteral lit)

-- | Translate the body of a monomorphic function.
translateBody ::
  ( GHC.MonadUnique m,
    ?freeVars :: [GHC.Var],
    ?inScopeSet :: GHC.InScopeSet
  ) =>
  GHC.CoreExpr ->
  TranslateT m Body
translateBody expr
  | GHC.exprIsDeadEnd expr = pure Bottom
translateBody expr@(GHC.Lam x body)
  | GHC.isId x = do
      let ?freeVars = x : ?freeVars
          ?inScopeSet = ?inScopeSet `GHC.extendInScopeSet` x

      Lam <$> translateVar x <*> translateBody body
  | otherwise = throwError (HigherRankedType Nothing)
translateBody (GHC.Case subject x ty alts)
  | GHC.Var y <- subject,
    y `elem` ?freeVars = do
      subject <- translateVar y

      let subst = GHC.mkOpenSubst ?inScopeSet [(x, GHC.Var y)]

      alts' <- mapM (translateAlt . substAlt subst) alts
      pure (Case subject alts')
  | otherwise = do
      -- Abstract over subject
      subj' <- translateExpr subject [] []
      body' <- translateExpr (GHC.Lam x (GHC.Case (GHC.Var x) x ty alts)) [] []
      pure (Body (App body' subj'))
translateBody (GHC.Let (GHC.NonRec x defn) body) = do
  -- Inline non-recursive let
  let subst = GHC.mkOpenSubst ?inScopeSet [(x, defn)]

  translateBody (GHC.substExpr subst body)
translateBody expr =
  Body <$> translateExpr expr [] []

-- | Translate a case alternative.
translateAlt ::
  ( GHC.MonadUnique m,
    ?freeVars :: [GHC.Var],
    ?inScopeSet :: GHC.InScopeSet
  ) =>
  GHC.CoreAlt ->
  TranslateT m Alt
translateAlt (GHC.Alt (GHC.DataAlt dataCon) xs rhs)
  | all GHC.isId xs = do
      let ?freeVars = xs ++ ?freeVars
          ?inScopeSet = 
            ?inScopeSet `GHC.extendInScopeSetList` xs

      ConAlt
        <$> translateDataCon dataCon
        <*> mapM translateVar xs
        <*> translateBody rhs
  | otherwise =
      throwError ExistentialType
translateAlt (GHC.Alt (GHC.LitAlt lit) _ rhs) = do
  lit' <- translateLit lit []
  rhs' <- translateBody rhs
  pure (LitAlt lit' rhs')
translateAlt (GHC.Alt GHC.DEFAULT _ rhs) =
  Default <$> translateBody rhs

-- * Clauses

exprToClause :: Monad m => [TyVar] -> [Var] -> Expr -> TranslateT m Clause
exprToClause as' xs' (App (App (Var x _) hyps) goal)
  | varName x == "==>" = do
      hyps' <- exprToHyps hyps
      goal' <- exprToEquation goal
      pure (mkClause as' xs' hyps' (Just goal'))
exprToClause as' xs' (App (Var x _) hyps)
  | varName x == "==>" = do
      hyps' <- exprToHyps hyps
      pure (mkClause as' xs' hyps' Nothing)
exprToClause as' xs' (App (App (Var x _) lhs) rhs)
  | varName x == "===" = do
      let goal = mkEquation lhs rhs
      pure (mkClause as' xs' [] (Just goal))
exprToClause _ _ _ =
  throwError ExpectedClause

exprToEquation :: Monad m => Expr -> TranslateT m Equation
exprToEquation (App (App (Var x _) lhs) rhs)
  | varName x == "===" = do
      pure (mkEquation lhs rhs)
exprToEquation _ =
  throwError ExpectedEquation

exprToHyps :: Monad m => Expr -> TranslateT m [Equation]
exprToHyps (App (App (Var x _) lhs) rhs)
  | varName x == "===" = do
      pure [mkEquation lhs rhs]
exprToHyps (App (App (Var x _) conj1) conj2)
  | varName x == "/\\" =
      (++) <$> exprToHyps conj1 <*> exprToHyps conj2
exprToHyps _ =
  throwError ExpectedHypotheses

-- * Utilities

-- | Errors encountered during translation.
data TranslationError
  = TypeLevelLiteral
  | HigherRankedType (Maybe GHC.Type)
  | CastOrCoercion
  | UnsupportedPrimitive GHC.TyCon
  | UnsupportedLiteral GHC.Literal
  | UnsupportedTyCon GHC.TyCon
  | ExistentialType
  | ExpectedEquation
  | ExpectedHypotheses
  | ExpectedClause

instance GHC.Outputable TranslationError where
  ppr TypeLevelLiteral = GHC.text "Type-level literals are not supported!"
  ppr (HigherRankedType Nothing) = 
    GHC.text "Higher-ranked types are not supported!"
  ppr (HigherRankedType (Just ty)) = 
    GHC.text "Higher-ranked types are not supported:" GHC.<+> GHC.ppr ty
  ppr CastOrCoercion = GHC.text "Casts or coercions are not supported!"
  ppr (UnsupportedPrimitive tyCon) =
    GHC.text "Unsupported primitive type:" GHC.<+> GHC.ppr tyCon
  ppr (UnsupportedLiteral lit) =
    GHC.text "Unsupported literal:" GHC.<+> GHC.ppr lit
  ppr (UnsupportedTyCon tyCon) =
    GHC.text "Unsupported type constructor:" GHC.<+> GHC.ppr tyCon
  ppr ExistentialType =
    GHC.text "Existential types and GADTs are not supported!"
  ppr ExpectedEquation =
    GHC.text "Expected an equation!"
  ppr ExpectedHypotheses =
    GHC.text "Expected a conjunction of equations!"
  ppr ExpectedClause =
    GHC.text "Expected a clause!"

-- | Enumerate free variables.
-- Type-level variables appear first.
freeVarsFrom :: (?freeVars :: [GHC.Var]) => [GHC.Var] -> [GHC.Var]
freeVarsFrom =
  reverse . List.intersect ?freeVars

-- | Create a fresh variable that abstracts over the given variables.
freshLiftVar :: GHC.MonadUnique m => String -> [GHC.Var] -> GHC.Type -> TranslateT m GHC.Id
freshLiftVar occName vars ty = do
  unique <- GHC.getUniqueM

  let occName' = occName ++ "_" ++ show unique
      name = GHC.mkSystemName unique (GHC.mkVarOcc occName')
  pure $ GHC.mkLocalId name GHC.Many (GHC.mkLamTypes vars ty)

-- | Apply a substitution to a case alternative.
substAlt :: GHC.Subst -> GHC.CoreAlt -> GHC.CoreAlt
substAlt subst (GHC.Alt con bndrs rhs) =
  let (subst', bndrs') = GHC.substBndrs subst bndrs
   in GHC.Alt con bndrs' (GHC.substExpr subst' rhs)
