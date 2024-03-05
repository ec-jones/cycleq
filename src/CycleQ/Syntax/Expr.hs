module CycleQ.Syntax.Expr
  ( -- * Expressions
    Var (..),
    Expr (..),
    Literal (..),
    mkApps,
    viewConApp,
    exprType,
    compareExpr,

    -- * Programs and Functions
    Program,
    Body (..),
    Alt (..),
    mkProgram,
    lookupProgram,

    -- * Substitutions and Contexts
    Subst,
    Context (..),
    composeSubst,
    substExpr,
    matchExpr,
    closeContext,
    subExprs,
  )
where

import Control.Applicative
import Control.Monad.State
import CycleQ.Syntax.Type
import CycleQ.Unique.Unique
import Data.Bifunctor
import Data.Foldable
import Data.Graph qualified as Graph
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Set qualified as Set

-- | A uniquely identifiable term-level variable.
data Var = MkVar
  { -- | The unique.
    varUnique :: !Unique,
    -- | The variable's name.
    varName :: String,
    -- | The variable's type.
    varType :: PolyType
  }
  deriving
    (Eq, Ord)
    via (ViaUnique Var)

instance HasUnique Var where
  getUnique = varUnique

  setUnique x unique =
    x {varUnique = unique}

instance Show Var where
  showsPrec _ x =
    showString (varName x)

-- | Literals for denoting primitive values.
data Literal
  = LitChar Char
  | LitInteger Integer
  | LitFloat Rational
  | LitDouble Rational
  deriving stock (Eq, Ord)

instance Show Literal where
  show (LitChar c) = show c
  show (LitInteger n) = show n
  show (LitFloat n) = show (fromRational n :: Float)
  show (LitDouble n) = show (fromRational n :: Double)

-- | Get the type of a literal expression.
literalType :: Literal -> Type
literalType (LitChar c) = LitTy TyLitChar
literalType (LitInteger n) = LitTy TyLitInteger
literalType (LitFloat n) = LitTy TyLitFloat
literalType (LitDouble n) = LitTy TyLitDouble

-- | Simple applicative expressions.
data Expr
  = Var Var [Type]
  | Con DataCon [Type]
  | Lit Literal
  | App Expr Expr
  deriving stock (Eq, Ord)

instance Show Expr where
  showsPrec _ (Var x tyArgs) = shows x
  showsPrec _ (Con dataCon tyArgs) = shows dataCon
  showsPrec _ (Lit lit) = shows lit
  showsPrec p (App fun arg) =
    showParen (p > 10) $
      shows fun . showChar ' ' . showsPrec 11 arg

-- | Get the type of an expression.
-- N.B. The expression is assumed to be well-typed.
exprType :: Expr -> Type
exprType (Var x tyArgs) =
  instantiatePolyType (varType x) tyArgs
exprType (Con dataCon tyArgs) =
  instantiatePolyType (dataConType dataCon) tyArgs
exprType (Lit lit) = literalType lit
exprType (App fun arg) =
  case exprType fun of
    FunTy argTy resTy -> resTy
    nonFun ->
      error "Expression is not well-typed!"

-- | Apply an expression to a series of arguments.
mkApps :: Expr -> [Expr] -> Expr
mkApps = foldl' App
{-# INLINE mkApps #-}

-- | Attempt to deconstruct a constructor lead application.
viewConApp :: Expr -> Maybe (DataCon, [Type], [Expr])
viewConApp = go []
  where
    go :: [Expr] -> Expr -> Maybe (DataCon, [Type], [Expr])
    go args (App fun arg) =
      go (arg : args) fun
    go args (Con con tyArgs) =
      pure (con, tyArgs, args)
    go _ _ = Nothing

-- | Compare expressions by function symbols.
compareExpr :: (?program :: Program) => Expr -> Expr -> Maybe Ordering
compareExpr expr1 expr2
  | expr1 == expr2 = Just EQ
  | let fs = freeVars expr1,  
    let gs = freeVars expr2,
      fs /= gs = 
        if compareDeps fs gs
          then Just GT
          else 
            if compareDeps gs fs
              then Just LT
              else Nothing
  | otherwise = Nothing

-- | Returns @True@ if the first set subsumes the second set.
-- That is, for any element in the second set that is not in the first,
-- there is a larger element in the first set that is not in the second.
compareDeps :: (?program :: Program) => Set.Set Var -> Set.Set Var -> Bool
compareDeps fs gs =
  all (\g -> any (\f -> f `precede` g) (fs Set.\\ gs)) (gs Set.\\ fs)

precede :: (?program :: Program) => Var -> Var -> Bool
precede x y =
  case Map.lookup x (programDependencies ?program) of
    Nothing ->
      case Map.lookup y (programDependencies ?program) of
        Nothing -> x > y -- Compare based on chronology
        Just _ -> True -- Local variables precede function symbols
    Just i ->
      case Map.lookup y (programDependencies ?program) of
        Nothing -> False -- Local variables precede function symbols
        Just j -> i > j -- Compare based on dependencies

-- * Programs and Functions

-- | A program is a collection of function definitions.
-- The quantified type variables appearing in the type are assumed to match those in the body.
data Program = Program {
  programDefinitions :: Map.Map Var ([TyVar], Body),
  programDependencies :: Map.Map Var Int -- ^ Topological sort of program dependencies
}

-- | The body of a function definition.
data Body
  = Lam Var Body
  | Case Var [Alt]
  | Body Expr
  | Bottom -- ^ An impossible branch of a case statement.

-- | A case alternative.
data Alt
  = Default Body
  | ConAlt DataCon [Var] Body
  | LitAlt Literal Body

instance Show Body where
  showsPrec _ (Lam x body) =
    showChar '\\' . shows x . showString " -> " . shows body
  showsPrec _ (Case x alts) =
    showString "case "
      . shows x
      . showString " of {"
      . foldr (\alt k -> shows alt . showString "; " . k) (showChar '}') alts
  showsPrec _ (Body expr) = shows expr
  showsPrec _ Bottom = showChar '⊥'

instance Show Alt where
  showsPrec _ (Default rhs) = showString "_ -> " . shows rhs
  showsPrec _ (ConAlt dataCon xs rhs) =
    shows dataCon
      . foldr
        ( \x k ->
            showChar ' ' . shows x . k
        )
        (showString " -> " . shows rhs)
        xs
  showsPrec _ (LitAlt lit rhs) =
    shows lit . showString " -> " . shows rhs

-- | Construct a program from a list of function definitions.
mkProgram :: Map.Map Var ([TyVar], Body) -> Program
mkProgram defs =
  let deps = topoSort defs
   in Program {
      programDefinitions = defs,
      programDependencies = 
        Map.fromList [ (x, i) | (i, xs) <- zip [0..] deps,
            x <- xs ]
   }

-- | Topologically sort program functions into recursive groups.
topoSort :: Map.Map Var ([TyVar], Body) -> [[Var]]
topoSort program =
  Graph.flattenSCC
    <$> Graph.stronglyConnComp
      [ (var, var, deps) |
       (var, (_, body)) <- Map.toList program, 
      let deps = Set.toList (freeVars body)
      ]

-- | Lookup the function definition associated with a given variable.
lookupProgram :: Var -> Program -> Maybe ([TyVar], Body)
lookupProgram x = Map.lookup x . programDefinitions

-- * Free Variables

-- | Objects that contain variables
class FreeVars a where
  freeVars :: a -> Set.Set Var

instance FreeVars Expr where
  freeVars :: Expr -> Set.Set Var
  freeVars (Var x tyArgs) = Set.singleton x
  freeVars (Con con tyArgs) = Set.empty
  freeVars (Lit lit) = Set.empty
  freeVars (App fun arg) =
    freeVars fun `Set.union` freeVars arg

instance FreeVars Body where
  freeVars :: Body -> Set.Set Var
  freeVars (Lam x body) =
    Set.delete x (freeVars body)
  freeVars (Case scrut alts) =
    Set.unions (fmap freeVars alts)
  freeVars (Body body) =
    freeVars body
  freeVars Bottom = Set.empty

instance FreeVars Alt where
  freeVars :: Alt -> Set.Set Var
  freeVars (Default body) =
    freeVars body
  freeVars (ConAlt con xs body) =
    freeVars body Set.\\ Set.fromList xs
  freeVars (LitAlt lit body) =
    freeVars body


-- * Substitutions and Contexts

-- | Expression level substitution.
type Subst = Map.Map Var Expr

-- | Composition of subsitutions.
composeSubst :: Subst -> Subst -> Subst
composeSubst theta theta' =
  fmap (substExpr Map.empty theta') theta

-- | Apply a substitution to an expression.
substExpr :: TySubst -> Subst -> Expr -> Expr
substExpr tyTheta theta = go
  where
    go :: Expr -> Expr
    go (Var x tyArgs) =
      case Map.lookup x theta of
        Nothing
          | Forall [] ty <- varType x ->
              Var (x {varType = Forall [] (substType tyTheta ty)}) []
          | otherwise ->
              Var x (substType tyTheta <$> tyArgs)
        Just expr
          | null tyArgs -> expr
          | otherwise ->
              error "Substitution is not well-formed!"
    go (Con con tyArgs) =
      Con con (substType tyTheta <$> tyArgs)
    go (Lit nonRubbishLit) = Lit nonRubbishLit
    go (App fun arg) =
      App (go fun) (go arg)

-- | Match the second expression with an instance of the first.
matchExpr :: [TyVar] -> [Var] -> Expr -> Expr -> Maybe (TySubst, Subst)
matchExpr patTyVars patVars patExpr expr = do
  tySubst <- matchType patTyVars (exprType patExpr) (exprType expr)
  execStateT (go patExpr expr) (tySubst, Map.empty)
  where
    go :: Expr -> Expr -> StateT (TySubst, Subst) Maybe ()
    go (Var x tyArgs) expr
      | x `elem` patVars = do
          gets (Map.lookup x . snd) >>= \case
            Nothing -> do
              goType (exprType (Var x [])) (exprType expr)
              modify $ second $ Map.insert x expr
            Just expr' ->
              guard (expr == expr')
      | Var y tyArgs' <- expr = do
          guard (x == y)
          zipWithM_ goType tyArgs tyArgs'
    go (Con dataCon tyArgs) (Con dataCon' tyArgs') = do
      guard (dataCon == dataCon')
      zipWithM_ goType tyArgs tyArgs'
    go (Lit lit) (Lit lit') =
      guard (lit == lit')
    go (App fun arg) (App fun' arg') = do
      go fun fun'
      go arg arg'
    go _ _ = empty

    goType :: Type -> Type -> StateT (TySubst, Subst) Maybe ()
    goType ty ty' = do
      (tySubst, subst) <- get

      let patTyVars' = patTyVars List.\\ Map.keys tySubst
      tySubst' <-
        lift $
          matchType patTyVars' (substType tySubst ty) (substType tySubst ty')

      put (tySubst <> tySubst', subst)

-- | A one-hole context.
data Context
  = Dot
  | AppL Context Expr
  | AppR Expr Context

-- | Conver a context back to an expression.
closeContext :: Expr -> Context -> Expr
closeContext hole = go
  where
    go :: Context -> Expr
    go Dot = hole
    go (AppL ctx arg) = App (go ctx) arg
    go (AppR fun ctx) = App fun (go ctx)

-- | Enumerate sub-expressions.
subExprs :: Expr -> [(Expr, Context)]
subExprs expr@(App fun arg) =
  (expr, Dot)
    : [(expr', AppL ctx arg) | (expr', ctx) <- subExprs fun]
    ++ [(expr', AppR fun ctx) | (expr', ctx) <- subExprs arg]
subExprs nonApp = [(nonApp, Dot)]
