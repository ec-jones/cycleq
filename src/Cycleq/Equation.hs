{-# LANGUAGE NamedFieldPuns #-}

module Cycleq.Equation where

import Data.Bifunctor
import GHC.Plugins

-- | A simple equation between core expressions.
data Equation = Equation
  { equationType :: Type,
    equationVars :: [Id],
    equationLeft :: CoreExpr,
    equationRight :: CoreExpr,
    -- | Is the equation visibly invalid?
    equationAbsurd :: Bool
  }

instance Outputable Equation where
  ppr Equation {equationVars, equationLeft, equationRight} =
    -- ppUnless (null equationVars)
    --  (forAllLit <+> interpp'SP equationVars GHC.Plugins.<> dot)
    --   <+>
    ppr equationLeft <+> text "≃" <+> ppr equationRight

-- | Apply a substitution to both sides of an equation.
substEquation :: Subst -> Equation -> Equation
substEquation subst eq =
  eq
    { equationLeft = substExpr subst (equationLeft eq),
      equationRight = substExpr subst (equationRight eq)
    }

-- | Subterms of either side of an equation
subtermEquation :: Equation -> [(CoreExpr, CoreExpr -> Equation)]
subtermEquation equation =
  let lefts = subterms (equationLeft equation)
      rights = subterms (equationRight equation)
   in fmap (second (\k expr -> equation {equationLeft = k expr})) lefts
        ++ fmap (second (\k expr -> equation {equationRight = k expr})) rights

-- | Subterms of a core expression.
subterms :: CoreExpr -> [(CoreExpr, CoreExpr -> CoreExpr)]
subterms (Var x) = [(Var x, id)]
subterms (Lit lit) = [(Lit lit, id)]
subterms (App fun arg) =
  (App fun arg, id) :
  fmap (second (\k expr -> App (k expr) arg)) (subterms fun)
    ++ fmap (second (\k -> App fun . k)) (subterms arg)
subterms (Lam x body) = (Lam x body, id) : fmap (second (\k -> Lam x . k)) (subterms body)
subterms (Let bind body) = (Let bind body, id) : fmap (second (\k -> Let bind . k)) (subterms body)
subterms _ = []

-- | Interpret a core expression as an equation.
fromCore :: CoreExpr -> Equation
fromCore srcExpr =
  case collectArgs body of
    (Var op, [ty, lhs, rhs])
      | occName op == mkVarOcc "≃" ->
        Equation
          { equationType = exprToType ty,
            equationVars = filter isId xs,
            equationLeft = lhs,
            equationRight = rhs,
            equationAbsurd = False
          }
    nonEq -> pprPanic "Couldn't interpret core expression as equation!" (ppr srcExpr)
  where
    (xs, body) = collectBinders srcExpr
