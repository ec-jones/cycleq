module CycleQ.Syntax.Type
  ( -- * Types
    TyVar (..),
    Type (..),
    PolyType (..),

    -- * Datatypes
    DataTypeEnv,
    DataType (..),
    DataCon (..),
    LiteralTy (..),

    -- * Substitutions
    TySubst,
    substType,
    matchType,
    instantiatePolyType,
    dataConInstArgTys,
  )
where

import Control.Applicative
import Control.Monad.State
import CycleQ.Unique.Unique
import Data.Foldable
import Data.List qualified as List
import Data.Map qualified as Map

-- | A uniquely identifiable type-level variable.
data TyVar = MkTyVar
  { -- | The unique.
    tyVarUnique :: !Unique,
    -- | The variable's original name.
    tyVarName :: String
  }
  deriving
    (Eq, Ord)
    via (ViaUnique TyVar)

instance HasUnique TyVar where
  getUnique = tyVarUnique

  setUnique a unique =
    a {tyVarUnique = unique}

instance Show TyVar where
  show = tyVarName

-- | A monomorphic type.
data Type
  = TyVar TyVar [Type]
  | DataTy DataType [Type]
  | LitTy LiteralTy
  | FunTy Type Type
  | -- | Partially instantiated function types.
    FunTy0
  | FunTy1 Type
  deriving stock (Eq, Ord)

instance Show Type where
  showsPrec p (TyVar a tyArgs) =
    showParen (p > 10 && not (null tyArgs)) $
      foldl' (\k tyArg -> k . showChar ' ' . showsPrec 11 tyArg) (shows a) tyArgs
  showsPrec p (DataTy dataType tyArgs) =
    showParen (p > 10 && not (null tyArgs)) $
      foldl' (\k tyArg -> k . showChar ' ' . showsPrec 11 tyArg) (shows dataType) tyArgs
  showsPrec p (FunTy argTy resTy) =
    showParen (p > 0) $
      showsPrec 1 argTy . showString " -> " . shows resTy
  showsPrec p FunTy0 = showString "(->)"
  showsPrec p (FunTy1 argTy) =
    showParen True $
      showsPrec 1 argTy . showString " ->"
  showsPrec p (LitTy litTy) = shows litTy

-- | A Hindley-Milner style polymorphic type.
data PolyType
  = Forall [TyVar] Type

instance Show PolyType where
  showsPrec _ (Forall as ty)
    | null as = shows ty
    | otherwise =
        showString "forall"
          . foldr
            ( \x k ->
                showChar ' ' . shows x . k
            )
            (showString ". " . shows ty)
            as

-- * Datatypes

-- | A datatype environment.
type DataTypeEnv =
  Map.Map DataType [DataCon]

-- | An algebraic datatype identifier.
data DataType = MkDataType
  { -- | The unique
    dataTypeUnique :: !Unique,
    -- | The datatype's name.
    dataTypeName :: String
  }
  deriving
    (Eq, Ord)
    via (ViaUnique DataType)

instance HasUnique DataType where
  getUnique = dataTypeUnique

  setUnique dataType unique =
    dataType {dataTypeUnique = unique}

instance Show DataType where
  show = dataTypeName

-- | A constructor of an algebraic datatype.
data DataCon = MkDataCon
  { -- | The unique
    dataConUnique :: !Unique,
    -- | The constructor's name.
    dataConName :: String,
    -- | The constructor's type.
    dataConType :: PolyType
  }
  deriving
    (Eq, Ord)
    via (ViaUnique DataCon)

instance HasUnique DataCon where
  getUnique = dataConUnique

  setUnique con unique =
    con {dataConUnique = unique}

instance Show DataCon where
  show = dataConName

-- | The types of primitive values.
data LiteralTy
  = TyLitChar
  | TyLitInteger
  | TyLitFloat
  | TyLitDouble
  deriving stock (Eq, Ord)

instance Show LiteralTy where
  show TyLitChar = "Char"
  show TyLitInteger = "Integer"
  show TyLitFloat = "Float"
  show TyLitDouble = "Double"

-- * Substitution

-- | A type-level substitution.
type TySubst = Map.Map TyVar Type

-- | Apply a substitution to a monomorphic type.
substType :: TySubst -> Type -> Type
substType tyTheta = go
  where
    go :: Type -> Type
    go ty@(TyVar a tyArgs) =
      case Map.lookup a tyTheta of
        Nothing -> ty
        Just ty' ->
          applyType ty' (fmap go tyArgs)
    go (DataTy dataType tyArgs) =
      DataTy dataType (fmap go tyArgs)
    go (FunTy argTy resTy) =
      FunTy (go argTy) (go resTy)
    go FunTy0 = FunTy0
    go (FunTy1 argTy) = FunTy1 (go argTy)
    go (LitTy litTy) = LitTy litTy

    applyType :: Type -> [Type] -> Type
    applyType ty [] = ty
    applyType (TyVar a tyArgs) tyArgs' =
      TyVar a (tyArgs ++ tyArgs')
    applyType (DataTy dataType tyArgs) tyArgs' =
      DataTy dataType (tyArgs ++ tyArgs')
    applyType FunTy0 [argTy] =
      FunTy1 argTy
    applyType FunTy0 [argTy, resTy] =
      FunTy argTy resTy
    applyType (FunTy1 argTy) [resTy] =
      FunTy argTy resTy
    applyType _ tyArgs =
      error "Types is not well-formed!"

-- | Match the second type with an instance of the first.
matchType :: [TyVar] -> Type -> Type -> Maybe TySubst
matchType patTyVars patTy ty = execStateT (go patTy ty) Map.empty
  where
    go :: Type -> Type -> StateT TySubst Maybe ()
    go (TyVar a tyArgs) ty
      | a `elem` patTyVars = do
          (ty', tyArgs') <- lift $ peelArgs (length tyArgs) ty

          theta <- get
          case Map.lookup a theta of
            Nothing -> do
              put (Map.insert a ty' theta)
              zipWithM_ go tyArgs tyArgs'
            Just ty'' -> do
              guard (ty'' == ty')
              zipWithM_ go tyArgs tyArgs'
      | TyVar a' tyArgs' <- ty = do
          guard (a == a')
          zipWithM_ go tyArgs tyArgs'
    go (DataTy dataType tyArgs) (DataTy dataType' tyArgs') = do
      guard (dataType == dataType')
      zipWithM_ go tyArgs tyArgs'
    go (FunTy argTy resTy) (FunTy argTy' resTy') = do
      go argTy argTy'
      go resTy resTy'
    go FunTy0 FunTy0 = pure ()
    go (FunTy1 argTy) (FunTy1 argTy') =
      go argTy argTy'
    go (LitTy litTy) (LitTy litTy') =
      guard (litTy == litTy')
    go _ _ = empty

    -- Remove the last n arguments from a type.
    peelArgs :: Int -> Type -> Maybe (Type, [Type])
    peelArgs n (TyVar a tyArgs)
      | n <= length tyArgs =
          let (pre, post) = List.splitAt (length tyArgs - n) tyArgs
           in Just (TyVar a pre, post)
    peelArgs n (DataTy dataType tyArgs)
      | n <= length tyArgs =
          let (pre, post) = List.splitAt (length tyArgs - n) tyArgs
           in Just (DataTy dataType pre, post)
    peelArgs n ty@(FunTy _ _)
      | n <= 0 = Just (ty, [])
    peelArgs n ty@(LitTy _)
      | n <= 0 = Just (ty, [])
    peelArgs _ _ = Nothing -- Insufficient arguments

-- | Instantiate a polymorphic type.
instantiatePolyType :: PolyType -> [Type] -> Type
instantiatePolyType (Forall as ty) tyArgs
  | length as == length tyArgs =
      let theta = Map.fromList (zip as tyArgs)
       in substType theta ty
  | otherwise = error "Insufficient type arguments!"

-- | Instantiate a constructors argument types.
dataConInstArgTys :: DataCon -> [Type] -> [Type]
dataConInstArgTys con tyArgs =
  go (instantiatePolyType (dataConType con) tyArgs)
  where
    go :: Type -> [Type]
    go (FunTy argTy resTy) =
      argTy : go resTy
    go nonFun = []
