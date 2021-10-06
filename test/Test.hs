module Test where

import Prelude ()
import Cycleq

id :: a -> a
id x = x

data List a
  = Nil
  | Cons a (List a)

map :: (a -> b) -> List a -> List b
-- map f Nil = Nil
-- map f (Cons x xs) = Cons (f x) (map f xs)
map f = go
  where
    go Nil = Nil
    go (Cons x xs) = Cons (f x) (go xs)

data Nat
  = Zero
  | Succ Nat

add :: Nat -> Nat -> Nat
add Zero     y = y
add (Succ x) y = Succ (add x y)

goal_mapId :: Equation
goal_mapId = map id ≃ id

-- goal_addZero :: Nat -> Equation
-- goal_addZero x = add x Zero ≃ x

-- goal_addComm :: Nat -> Nat -> Equation
-- goal_addComm x y = add x y ≃ add y x

-- goal_addAssoc :: Nat -> Nat -> Nat -> Equation
-- goal_addAssoc x y z = add x (add y z) ≃ add (add x y) z