{-# LANGUAGE NamedFieldPuns #-}

module Cycleq.Equation where

import GHC.Plugins
import Data.Bifunctor

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
  ppr Equation {equationLeft, equationRight} =
    ppr equationLeft <+> text "≃" <+> ppr equationRight

-- | Apply a substitution to both sides of an equation.
substEquation :: Subst -> Equation -> Equation
substEquation subst eq = eq {
  equationLeft = substExpr subst (equationLeft eq),
  equationRight = substExpr subst (equationRight eq)
}

subtermEquation :: Equation -> [(CoreExpr, CoreExpr -> Equation)]
subtermEquation equation =
  let lefts = subterms (equationLeft equation)
      rights = subterms (equationRight equation)
  in fmap (second (\k expr -> equation { equationLeft = k expr })) lefts ++ 
        fmap (second (\k expr -> equation { equationRight = k expr })) rights

-- | Subterms of a core expression.
subterms :: CoreExpr -> [(CoreExpr, CoreExpr -> CoreExpr)]
subterms (Var x) = [(Var x, id)]
subterms (Lit lit) = [(Lit lit, id)]
subterms (App fun arg) = (App fun arg, id) : (subterms fun ++ subterms arg)
subterms (Lam x body) = (Lam x body, id) : subterms body
subterms (Let bind body) = (Let bind body, id) : subterms body
subterms _ = []

-- | Interpret a core expression as an equation.
fromCore :: CoreExpr -> Equation
fromCore srcExpr =
  case collectArgs body of
    (Var op, [ty, lhs, rhs])
      | occName op == mkVarOcc "≃" ->
        Equation
              { equationType = exprToType ty,
                equationVars = xs,
                equationLeft = cleanCore lhs,
                equationRight = cleanCore rhs,
                equationAbsurd = False
              }
    nonEq -> pprPanic "Couldn't interpret core expression as equation!" (ppr srcExpr)
  where
    (xs, body) = collectBinders srcExpr

-- | Remove any ticks, cast, coercsions or types from a core expression.
cleanCore :: CoreExpr -> CoreExpr
cleanCore (Var x) = Var x
cleanCore (Lit lit) = Lit lit
cleanCore (App fun arg)
  | isValArg arg = App (cleanCore fun) (cleanCore arg)
  | otherwise = cleanCore fun
cleanCore (Lam x body)
  | isId x = Lam x (cleanCore body)
  | otherwise = cleanCore body
cleanCore (Let bind body) = Let (cleanBind bind) (cleanCore body)
cleanCore (Case scrut x ty cases) = Case (cleanCore scrut) x ty (map cleanAlt cases)
cleanCore (Cast expr _) = cleanCore expr
cleanCore (Tick _ expr) = cleanCore expr
cleanCore srcExpr = pprPanic "Couldn't clean core expression!" (ppr srcExpr)

-- | Clean every expression in a program.
cleanBind :: CoreBind -> CoreBind
cleanBind (NonRec x defn) = NonRec x (cleanCore defn)
cleanBind (Rec defns) = Rec (map (second cleanCore) defns)

-- | Clean case alternative.
cleanAlt :: CoreAlt -> CoreAlt
cleanAlt (ac, xs, rhs) = (ac, xs, cleanCore rhs)