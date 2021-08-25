module Test where

import Cycleq

id :: a -> a
id x = x

data Nat
  = Zero
  | Succ Nat

data List a
  = Nil
  | Cons a (List a)

map :: (a -> b) -> List a -> List b
map f Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

reverse :: List a -> List a
reverse Nil = Nil
reverse (Cons x xs) = snoc x (reverse xs)

snoc :: a -> List a -> List a
snoc x Nil = Cons x Nil
snoc x (Cons y ys) = Cons y (snoc x ys)

take :: Nat -> List a -> List a
take Zero _ = Nil
take (Succ n) Nil = Nil
take (Succ n) (Cons x xs) = Cons x (take n xs)

commands :: [Command]
commands =
  [ normaliseTerm (\y ys zs -> [zs ≃ Cons y ys] ⊢ map id zs),
    criticalTerms (\n xs -> [] ⊢ take (Succ n) (reverse xs)),
    simplifyEquation (\y ys zs -> [zs ≃ Cons y ys] ⊢ map id zs ≃ Cons y ys),
    simplifyEquation (\y ys -> [] ⊢ Nil ≃ Cons y ys),
    simplifySequent (\y ys zs -> [Cons y ys ≃ map id zs] ⊢ Cons y ys ≃ zs)
  ]