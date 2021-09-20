module Test where

import Cycleq

id :: a -> a
id x = x

data List a
  = Nil
  | Cons a (List a)

map :: (a -> b) -> List a -> List b
map f Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

main :: Equation
main = map id ≃ id