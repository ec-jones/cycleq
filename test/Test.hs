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

data Nat
  = Zero
  | Succ Nat

add :: Nat -> Nat -> Nat
add Zero m = m
add (Succ n) m = Succ (add n m)

commands :: [Command]
commands =
  [ normalise (\y ys zs -> [zs ≃ Cons y ys] ⊢ map id zs),
    criticalTerms (\n m -> add (add n Zero) (Succ m))
  ]