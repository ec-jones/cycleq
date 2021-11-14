module Mutual where

import Prelude (Int)
import Cycleq

id :: a -> a
id x = x

comp :: (b -> c) -> (a -> b) -> a -> c
comp f g x = f (g x)

data Tm a =
  Var a | Cst Int | App (Expr a) (Expr a)

data Expr a = MkExpr (Tm a) Int

mapE :: (a -> b) -> Expr a -> Expr b
mapE f (MkExpr t n) = MkExpr (mapT f t) n

mapT :: (a -> b) -> Tm a -> Tm b
mapT f (Var n) = Var (f n)
mapT f (Cst n) = Cst n
mapT f (App e1 e2) = App (mapE f e1) (mapE f e2)

goal_mapE_id :: Expr a -> Equation
goal_mapE_id e = mapE id e ≃ e