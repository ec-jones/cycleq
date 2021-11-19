module M2 where

import Cycleq
import Prelude ()

data Nat = Z | S Nat
data B = T | F

not :: B -> B
not T = F
not F = T

f :: Nat -> B
f Z = F
f (S n) = g n

g :: Nat -> B
g Z = T
g (S n) = f n

h :: Nat -> B
h Z = F
h (S n) = not (h n)

goal_1 :: Nat -> Equation
goal_1 n = h n ≃ f n 