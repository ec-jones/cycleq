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
    ppr (cleanCore True equationLeft) <+> text "≃" <+> ppr (cleanCore True equationRight)

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
    (xs, body) = collectBinders (cleanCore False srcExpr)

-- | Remove any ticks, cast, coercsions or types from a core expression.
cleanCore :: Bool -> CoreExpr -> CoreExpr
cleanCore p (Var x) = Var x
cleanCore p (Lit lit) = Lit lit
cleanCore p (App fun arg)
  | isValArg arg || not p = App (cleanCore p fun) (cleanCore p arg)
  | otherwise = cleanCore p fun
cleanCore p (Lam x body)
  | isId x || not p = Lam x (cleanCore p body)
  | otherwise = cleanCore p body
cleanCore p (Let bind body) = Let (cleanBind p bind) (cleanCore p body)
cleanCore p (Case scrut x ty cases) = Case (cleanCore p scrut) x ty (map (cleanAlt p) cases)
cleanCore p (Cast expr _) = cleanCore p expr
cleanCore p (Tick _ expr) = cleanCore p expr
cleanCore p (Type ty) = Type ty
cleanCore p srcExpr = pprPanic "Couldn't clean core expression!" (ppr srcExpr)

-- | Clean every expression in a program.
cleanBind :: Bool -> CoreBind -> CoreBind
cleanBind p (NonRec x defn) = NonRec x (cleanCore p defn)
cleanBind p (Rec defns) = Rec (map (second $ cleanCore p) defns)

-- | Clean case alternative.
cleanAlt :: Bool -> CoreAlt -> CoreAlt
cleanAlt p (ac, xs, rhs) = (ac, xs, cleanCore p rhs)
