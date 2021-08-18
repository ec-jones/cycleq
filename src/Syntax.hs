{-# LANGUAGE FlexibleInstances #-}

module Syntax
  ( Syntax (..),

    -- * Equations and Sequents
    Equation (..),
    (≃),
    Sequent (..),
    (⊢),

    -- * Commands
    Command (..),
    normalise,
    criticalTerms,
    isProductive,
  )
where

import Data.Bifunctor
import GHC.Plugins

-- | The class of cycleq syntax that can be decoded from core expressions.
class Syntax a where
  decodeCore :: CoreExpr -> a

-- | Decode a list of core expressions.
-- N.B. This instance relies on rewriting being turned off!
instance Syntax a => Syntax [a] where
  decodeCore srcExpr =
    case collectArgs srcExpr of
      (Var cons, [_, x, xs])
        | occName cons == mkVarOcc ":" ->
          decodeCore x : decodeCore xs
      (Var nil, [_])
        | occName nil == mkVarOcc "[]" -> []
      _ -> pprPanic "Couldn't interpret expression as a list!" (ppr srcExpr)

-- | Strip ticks, casts, types, and coercions from a core expression.
instance Syntax CoreExpr where
  decodeCore (Var x) = Var x
  decodeCore (Lit lit) = Lit lit
  decodeCore (App fun arg)
    | isValArg arg = App (decodeCore fun) (decodeCore arg)
    | otherwise = decodeCore fun
  decodeCore (Lam x body)
    | isId x = Lam x (decodeCore body)
    | otherwise = decodeCore body
  decodeCore (Let bind body) = Let (stripBind bind) (decodeCore body)
    where
      stripBind (NonRec x defn) = NonRec x (decodeCore defn)
      stripBind (Rec defns) = Rec (map (second decodeCore) defns)
  decodeCore (Case scrut x ty cases) = Case (decodeCore scrut) x ty (map stripAlt cases)
    where
      stripAlt (ac, xs, rhs) = (ac, xs, decodeCore rhs)
  decodeCore (Cast expr _) = decodeCore expr
  decodeCore (Tick _ expr) = decodeCore expr
  decodeCore srcExpr = pprPanic "Unexpected top-level type or coercion!" (ppr srcExpr)

-- * Equations and Sequents

-- | A simple equation between core expressions.
data Equation
  = Equation CoreExpr CoreExpr

(≃) :: a -> a -> Equation
{-# NOINLINE (≃) #-}
(≃) = undefined

instance Outputable Equation where
  ppr (Equation lhs rhs) = ppr lhs <+> text "≃" <+> ppr rhs

instance Syntax Equation where
  decodeCore srcExpr =
    case collectArgs srcExpr of
      (Var eq, [_, lhs, rhs])
        | occName eq == mkVarOcc "≃" ->
          Equation (decodeCore lhs) (decodeCore rhs)
      nonEq -> pprPanic "Couldn't interpret expression as an equation!" (ppr srcExpr)

-- | A command or equation under a set of assumptions.
data Sequent a = Sequent
  { univVars :: [Var],
    antecedent :: [Equation],
    consequent :: a
  }

(⊢) :: [Equation] -> a -> Sequent a
{-# NOINLINE (⊢) #-}
(⊢) = undefined

instance Outputable a => Outputable (Sequent a) where
  ppr = error "unimplemented!"

-- | N.B. Top-level lambdas are interpreted as universal quantifiers.
-- That is, the variable @x@ is treated as free when normalising @expr@ with the command @normalise (\ x -> expr)@.
instance Syntax a => Syntax (Sequent a) where
  decodeCore srcExpr =
    let (xs, body) = collectBinders srcExpr
     in case collectArgs body of
          (Var eq, [_, ante, cons])
            | occName eq == mkVarOcc "⊢" ->
              Sequent xs (decodeCore ante) (decodeCore cons)
          nonEq -> Sequent xs [] (decodeCore body)

-- * Commands

-- | A command for the Cycleq system to execute.
data Command
  = Normalise (Sequent CoreExpr)
  | CriticalTerms (Sequent CoreExpr)
  | IsProductive (Sequent CoreExpr)

-- | Normalise a core expression under a set of unconditional equations.
-- Equations are applied eagerly and so should be confluent.
normalise :: a -> Command
{-# NOINLINE normalise #-}
normalise = undefined

-- | Recursively analyse which expressions are preventing reduction to a constructor.
criticalTerms :: a -> Command
{-# NOINLINE criticalTerms #-}
criticalTerms = undefined 

-- | Check whether a core expression can be reduce to a constructor finite case analysis.
isProductive :: a -> Command
{-# NOINLINE isProductive #-}
isProductive = undefined 

instance Syntax Command where
  decodeCore srcExpr =
    case collectArgs srcExpr of
      (Var commandType, [_, sequent])
        | occName commandType == mkVarOcc "normalise" ->
          Normalise (decodeCore sequent)
      (Var commandType, [_, sequent])
        | occName commandType == mkVarOcc "criticalTerms" ->
          CriticalTerms (decodeCore sequent)
      (Var commandType, [_, sequent])
        | occName commandType == mkVarOcc "isProductive" ->
          CriticalTerms (decodeCore sequent)
      _ -> pprPanic "Couldn't interpret expression as command!" (ppr srcExpr)