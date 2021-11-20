module M where

import Prelude ()
import Cycleq

data Nat
  = Z
  | S Nat

id :: a -> a
id x = x

comp :: (b -> c) -> (a -> b) -> a -> c
comp f g x = f (g x)

data Tm a =
  Var a | Cst Nat | App (Expr a) (Expr a)

data Expr a = MkExpr (Tm a) Nat

mapE :: (a -> b) -> Expr a -> Expr b
mapE f (MkExpr t n) = MkExpr (mapT f t) n

mapT :: (a -> b) -> Tm a -> Tm b
mapT f (Var n) = Var (f n)
mapT f (Cst n) = Cst n
mapT f (App e1 e2) = App (mapE f e1) (mapE f e2)

mapA :: (Nat -> Nat) -> Expr a -> Expr a
mapA f (MkExpr t n) = MkExpr (mapA' f t) (f n)

mapA' :: (Nat -> Nat) -> Tm a -> Tm a
mapA' f (Var x) = Var x
mapA' f (Cst x) = Cst x
mapA' f (App e1 e2) = App (mapA f e1) (mapA f e2)

headE :: Expr a -> Expr a
headE (MkExpr (Var x) n) = MkExpr (Var x) n
headE (MkExpr (Cst x) n) = MkExpr (Cst x) n
headE (MkExpr (App e1 e2) n) = headE e1

data List a
  = Nil
  | Cons a (List a)

map :: (a -> b) -> List a -> List b
map f Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

app :: List a -> List a -> List a
app Nil ys = ys
app (Cons x xs) ys = Cons x (app xs ys)

argsE :: Expr a -> List (Expr a)
argsE (MkExpr t n) = argsT t

argsT :: Tm a -> List (Expr a)
argsT (Var x) = Nil
argsT (Cst n) = Nil
argsT (App e1 e2) = Cons e2 (argsE e1)

prop_1 :: Expr a -> Equation
prop_1 e = mapE id e === e

prop_2 :: (b -> c) -> (a -> b) -> Expr a -> Equation
prop_2 f g e =
  mapE (f `comp` g) e === mapE f (mapE g e)

prop_3 :: (a -> b) -> Expr a -> Equation
prop_3 f e =
  argsE (mapE f e) === map (mapE f) (argsE e)

prop_4 :: (a -> b) -> Tm a -> Equation
prop_4 f e =
  argsT (mapT f e) === map (mapE f) (argsT e)

prop_5 :: (a -> b) -> Expr a -> Equation
prop_5 f e =
  headE (mapE f e) === mapE f (headE e)