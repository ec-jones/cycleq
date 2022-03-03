{-# LANGUAGE TemplateHaskellQuotes #-}

module Scratch where

import Prelude ()
import CycleQ

data Nat
  = Z
  | S Nat

data List a
  = Nil
  | Cons a (List a)

map :: (a -> b) -> List a -> List b
map f Nil = Nil
map f (Cons x xs) =
  Cons (f x) (map f xs)

length :: List a -> Nat
length Nil = Z
length (Cons x xs) = 
  S (length xs)

add :: Nat -> Nat -> Nat
add Z m = m
add (S n) m =
  S (add n m)

addZero :: Nat -> Equation
addZero n =
  add n Z === n

{-# ANN mapLength defaultParams { fuel = 4, lemmas = ['addZero], output = "proofs/mapLength.svg" } #-}
mapLength :: (a -> b) -> List a -> Equation
mapLength f xs =
  length (map f xs) === add (length xs) Z