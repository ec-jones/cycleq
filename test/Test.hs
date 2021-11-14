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
map f = go
  where
    go Nil = Nil
    go (Cons x xs) = Cons (f x) (go xs)

-- goal_mapId :: Equation
-- goal_mapId = map id ≃ id

-- goal_mapComp :: (b -> c) -> (a -> b) -> List a -> Equation
-- goal_mapComp f g xs =
--   map (f . g) xs ≃ map f (map g xs)

goal_mapComp :: (a -> b) -> (b -> c) -> List a -> Equation
goal_mapComp g f xs = map (f . g) xs ≃ map f (map g xs)