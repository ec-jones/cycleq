module Test where

import Prelude ()
import Cycleq

id :: a -> a
id x = x

(.) :: (b -> c) -> (a -> b) -> a -> c
(f . g) x = f (g x)

data List a
  = Nil
  | Cons a (List a)

map :: (a -> b) -> List a -> List b
map f Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

data Nat
  = Zero
  | Succ Nat

add :: Nat -> Nat -> Nat
add Zero     y = y
add (Succ x) y = Succ (add x y)

main :: Equation
main = map id ≃ id

-- main :: (b -> c) -> (a -> b) -> Equation
-- main f g = map (f . g) ≃ map f . map g

-- main :: Nat -> Equation
-- main x = add x Zero ≃ x

-- main :: Nat -> Nat -> Equation
-- main x y = add x y ≃ add y x

-- main :: Nat -> Nat -> Nat -> Equation
-- main x y z = add x (add y z) ≃ add (add x y) z