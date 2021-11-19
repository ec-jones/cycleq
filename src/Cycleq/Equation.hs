{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}

-- |
-- Module: Cycleq.Equation
module Cycleq.Equation
  ( -- * Equations
    Equation (..),
    pprQualified,
    prune,
    equationFromCore,

    -- * Subexpressions
    SubExpr,
    withSubExpr,
    exprSubExprs,
    equationSubExprs,
    isVariableSubExpr,
  )
where

import Control.Applicative
import Data.Bifunctor
import GHC.Plugins hiding (empty)

-- * Equations

-- | An equation between core expressions.
data Equation
  = Equation
      [Id]
      -- ^ Universally quantified variables.
      CoreExpr
      -- ^ Left-hand side of the equation.
      CoreExpr
      -- ^ Right-hand side of the equation.

instance Outputable Equation where
  ppr (Equation xs lhs rhs) =
    pprUserExpr id lhs <+> text "===" <+> pprUserExpr id rhs

-- | Print an equation with explicit variable quantification.
pprQualified :: Equation -> SDoc
pprQualified eq@(Equation xs _ _)
  | not (null xs) = char '∀' <+> interpp'SP xs GHC.Plugins.<> dot <+> ppr eq
  | otherwise = ppr eq

-- | Remove redundant equations.
prune :: Equation -> Equation
prune (Equation _ lhs rhs) =
  let xs = exprFreeVarsDSet lhs 
      ys = exprFreeVarsDSet rhs
  in Equation (dVarSetElems (unionDVarSet xs ys)) lhs rhs

-- | Print CoreExpr compactly without metadata.
pprUserExpr :: (SDoc -> SDoc) -> CoreExpr -> SDoc
pprUserExpr f (Var x) = ppr (occName x)
pprUserExpr f (Lit lit) = pprLiteral f lit
pprUserExpr f expr@(Lam _ _) =
  let (_, bndrs, body) = collectTyAndValBinders expr
      bndrs' = filter isId bndrs
   in f $
        hang
          (char 'λ' GHC.Plugins.<> interppSP (map occName bndrs') <+> char '→')
          2
          (pprUserExpr id body)
pprUserExpr f expr@(App _ _) =
  let (fun, args) = collectArgs expr
      args' = filter isValArg args
      ppArgs = sep (map (pprUserExpr parens) args')
   in if null args'
        then pprUserExpr id fun
        else f $ hang (pprUserExpr parens fun) 2 ppArgs
pprUserExpr f (Let _ expr) = pprUserExpr f expr
pprUserExpr _ expr = pprPanic "Unsupported expression" (ppr expr)

-- | Construct an equation from a core expression of the form @\\x1 ... xn -> lhs ≃ rhs@.
equationFromCore :: CoreExpr -> Maybe Equation
equationFromCore expr
  | let (xs, body) = collectBinders expr,
    (Var eq, [ty, lhs, rhs]) <- collectArgs body,
    occName eq == mkVarOcc "===" =
    Just (Equation (filter isId xs) lhs rhs)
  | otherwise = Nothing

-- * Subexpressions.

-- | A subexpression within a larger context of type @a@.
data SubExpr a
  = SubExpr
      CoreExpr
      (CoreExpr -> a)
  deriving stock (Functor)

-- | Modify a subexpression.
withSubExpr :: Functor f => SubExpr a -> (CoreExpr -> f (b, CoreExpr)) -> f (b, a)
withSubExpr (SubExpr expr ctx) f = second ctx <$> f expr

-- | The trivial subexpression.
root :: CoreExpr -> SubExpr CoreExpr
root expr = SubExpr expr id

-- | Enumerate applicative subexpressions (i.e. not case altneratives) of a core expression.
exprSubExprs :: Alternative f => CoreExpr -> f (SubExpr CoreExpr)
exprSubExprs (Var x) = pure (root (Var x))
exprSubExprs (Lit lit) = pure (root (Lit lit))
exprSubExprs (App fun arg) =
  pure (root (App fun arg))
    <|> fmap (`App` arg) <$> exprSubExprs fun
    <|> fmap (App fun) <$> exprSubExprs arg
exprSubExprs (Lam x body) =
  pure (root (Lam x body))
    <|> fmap (Lam x) <$> exprSubExprs body
exprSubExprs (Let bind body) =
  pure (root (Let bind body))
    <|> fmap (Let bind) <$> exprSubExprs body
exprSubExprs nonApp = empty

-- | Enumerate applicative subexpressions of either side of an equation.
equationSubExprs :: Alternative f => Equation -> f (SubExpr Equation)
equationSubExprs (Equation xs lhs rhs) =
  fmap (flip (Equation xs) rhs) <$> exprSubExprs lhs
    <|> fmap (Equation xs lhs) <$> exprSubExprs rhs

-- | Is the subexpression a variable?
isVariableSubExpr :: SubExpr a -> Bool
isVariableSubExpr (SubExpr (Var _) _) = True
isVariableSubExpr nonVar = False
