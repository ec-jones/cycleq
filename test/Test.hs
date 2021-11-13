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

-- goal_mapId :: Equation
-- goal_mapId = map id ≃ id

goal_mapComp :: (b -> c) -> (a -> b) -> List a -> Equation
goal_mapComp f g xs =
  map (f . g) xs ≃ map f (map g xs)