module Z where

import Prelude ()
import Cycleq

data Bool
  = False
  | True

not :: Bool -> Bool
not False = False
not True = True

data List a
  = Nil
  | Cons a (List a)

butlast :: List a -> List a
butlast Nil = Nil
butlast (Cons x Nil) = Nil
butlast (Cons x xs) = Cons x (butlast xs)

butlastConcat :: List a -> List a -> List a
butlastConcat Nil xs = butlast xs
butlastConcat xs@(Cons _ _) ys = app xs (butlast ys)

app :: List a -> List a -> List a
app Nil ys = ys
app (Cons x xs) ys = Cons x (app xs ys)

map :: (a -> b) -> List a -> List b
map f Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

filter :: (a -> Bool) -> List a -> List a 
filter p Nil = Nil
filter p (Cons x xs) =
  case p x of
    True -> Cons x (filter p xs)
    False -> filter p xs

dropWhile :: (a -> Bool) -> List a -> List a
dropWhile f Nil = Nil
dropWhile f (Cons x xs) =
  case f x of
    False -> Cons x xs
    True -> dropWhile f xs

takeWhile :: (a -> Bool) -> List a -> List a
takeWhile f Nil = Nil
takeWhile f (Cons x xs) =
  case f x of
    True -> Cons x (takeWhile f xs)
    False ->  Nil

delete :: Nat -> List Nat -> List Nat
delete n Nil = Nil
delete n (Cons m xs) =
  case n `eq` m of
    True -> delete n xs
    False -> Cons m (delete n xs)

len :: List a -> Nat
len Nil = Z
len (Cons x xs) = S (len xs)

elem :: Nat -> List Nat -> Bool
elem n Nil = False
elem n (Cons x xs) =
  case n `eq` x of
    True -> True
    False -> elem n xs

insert :: Nat -> List Nat -> List Nat
insert n Nil = Cons n Nil
insert n (Cons m xs) =
  case n `lq` m of
    True -> Cons n (Cons m xs)
    False -> Cons m (insert n xs)

isort :: List Nat -> List Nat
isort Nil = Nil
isort (Cons x xs) = insert x (isort xs)

zip :: List a -> List b -> List (a, b)
zip Nil _ = Nil
zip _ Nil = Nil
zip (Cons x xs) (Cons y ys) = Cons (x, y) (zip xs ys)

zipConcat :: a -> List a -> List a -> List (a, a)
zipConcat x xs Nil = Nil
zipConcat x xs (Cons y ys) =
  Cons (x, y) (zip xs ys)

data Nat
  = Z
  | S Nat

take :: Nat -> List a -> List a
take Z _ = Nil
take (S n) Nil = Nil
take (S n) (Cons x xs) = Cons x (take n xs)

drop :: Nat -> List a -> List a
drop Z xs = xs
drop (S n) Nil = Nil 
drop (S n) (Cons x xs) = drop n xs

count :: Nat -> List Nat -> Nat
count n Nil = Z
count n (Cons m ms) =
  case n `eq` m of
    True -> S (count n ms)
    False -> count n ms

eq :: Nat -> Nat -> Bool
eq Z Z = True
eq Z (S _) = False
eq (S n) (S m) = True
eq (S _) Z = False

add :: Nat -> Nat -> Nat
add Z n = n
add (S n) m = S (add n m)

max :: Nat -> Nat -> Nat
max Z m = m
max (S n) Z = S n
max (S n) (S m) = S (max n m)

min :: Nat -> Nat -> Nat
min Z m = Z
min (S n) Z = Z
min (S n) (S m) = S (min n m)

lq :: Nat -> Nat -> Bool
lq Z _ = True
lq (S _) Z = False
lq (S x) (S y) = lq x y

lt :: Nat -> Nat -> Bool
lt Z Z = False
lt Z (S x) = True
lt (S _) Z = False
lt (S x) (S y) = lt x y

minus :: Nat -> Nat -> Nat
minus n Z = n
minus Z (S m) = Z
minus (S n) (S m) = minus n m 

data Tree a
  = Leaf
  | Node a (Tree a) (Tree a)

height :: Tree a -> Nat
height Leaf = Z
height (Node x l r) = S (max (height l) (height r))

mirror :: Tree a -> Tree a
mirror Leaf = Leaf
mirror (Node x l r) = Node x (mirror l) (mirror r)

rev :: List a -> List a
rev Nil = Nil
rev (Cons x xs) = snoc x (rev xs)

snoc :: a -> List a -> List a
snoc x Nil = Cons x Nil
snoc x (Cons y ys) = Cons y (snoc x ys)

-- goal_1 :: Nat -> List a -> Equation
-- goal_1 n xs = app (take n xs) (drop n xs) ≃ xs

-- goal_2 :: Nat -> List Nat -> List Nat -> Equation
-- goal_2 n xs ys =
--   add (count n xs) (count n ys) ≃ count n (app xs ys)

-- goal_3 :: Nat -> List Nat -> List Nat -> Equation
-- goal_3 n xs ys = 
--   lq (count n xs) (count n (app xs ys)) ≃ True

-- goal_4 :: Nat -> List Nat -> Equation
-- goal_4 n xs =
--   count n (Cons n xs) ≃ S (count n xs)

-- goal_6 :: Nat -> Nat -> Equation
-- goal_6 n m =
--   minus n (add n m) ≃ Z

-- goal_7 :: Nat -> Nat -> Equation
-- goal_7 n m =
--   minus (add n m) n ≃ m
  
-- goal_8 :: Nat -> Nat -> Nat -> Equation   
-- goal_8 n m k = 
  -- minus (add k m) (add k n) ≃ minus m n
  
-- goal_9 :: Nat -> Nat -> Nat -> Equation   
-- goal_9 n m k = 
  -- minus (minus n m) k ≃ minus n (add m k)

-- goal_10 :: Nat -> Equation   
-- goal_10 n = 
--   minus n n ≃ Z

-- goal_11 :: List a -> Equation
-- goal_11 xs =
--   drop Z xs ≃ xs 

-- goal_12 :: (a -> b) -> Nat -> List a -> Equation
-- goal_12 f n xs =
--   drop n (map f xs) ≃ map f (drop n xs)

-- goal_13 :: Nat -> a -> List a -> Equation
-- goal_13 n x xs =
--   drop (S n) (Cons x xs) ≃ drop n xs

-- FAIL
-- goal_14 :: (a -> Bool) -> List a -> List a -> Equation
-- goal_14 p xs ys =
--   filter p (app xs ys) ≃ 
--     app (filter p xs) (filter p ys)

-- FAIL
-- goal_15 :: Nat -> List Nat -> Equation
-- goal_15 n xs =
--   len (insert n xs) ≃ S (len xs)

-- goal_18 :: Nat -> Nat -> Equation
-- goal_18 n m =
--   lt n (S (add n m)) ≃ True 

-- goal_19 :: Nat -> List Nat -> Equation
-- goal_19 n xs =
--   len (drop n xs) ≃ minus (len xs) n

-- FAIL
-- goal_20 :: List Nat -> Equation
-- goal_20 xs =
--   len (isort xs) ≃ len xs

-- goal_21 :: Nat -> Nat -> Equation
-- goal_21 n m =
--   lq n (add n m) ≃ True 

-- goal_22 :: Nat -> Nat -> Nat -> Equation
-- goal_22 n m k =
--   max (max n m) k ≃ max n (max m k)

-- goal_23 :: Nat -> Nat -> Equation
-- goal_23 n m =
--   max n m ≃ max m n 

-- goal_28 :: Nat -> List Nat -> Equation
-- goal_28 n xs =
--   elem n (app xs (Cons n Nil)) ≃ True

-- FAIL (goal_30)
-- goal_29 :: Nat -> List Nat -> Equation
-- goal_29 n xs =
--   elem n (insert n xs) ≃ True 

-- goal_31 :: Nat -> Nat -> Nat -> Equation
-- goal_31 n m k =
--   min (min n m) k ≃ min n (min m k)

-- goal_32 :: Nat -> Nat -> Equation
-- goal_32 n m =
--   min n m ≃ min m n

-- goal_35 :: List a -> Equation
-- goal_35 xs =
--   dropWhile (\x -> False) xs ≃ xs

-- goal_36 :: List a -> Equation
-- goal_36 xs =
--   takeWhile (\x -> True) xs ≃ xs

-- FAIL
-- goal_37 :: Nat -> List Nat -> Equation
-- goal_37 n xs =
--   not (elem n (delete n xs)) ≃ True

-- goal_38 :: Nat -> List Nat -> Equation
-- goal_38 n xs =
--   count n (app xs (Cons n Nil)) ≃ 
--     S (count n xs)

-- goal_39 :: Nat -> Nat -> List Nat -> Equation
-- goal_39 n x xs = 
--   add (count n (Cons x Nil)) (count n xs) ≃ count n (Cons x xs)

-- goal_40 :: List Nat -> Equation
-- goal_40 xs =
--   take Z xs ≃ Nil

-- goal_41 :: Nat -> (a -> b) -> List a -> Equation
-- goal_41 n f xs =
--   take n (map f xs) ≃ map f (take n xs)

-- goal_42 :: Nat -> Nat -> List Nat -> Equation
-- goal_42 n x xs =
--   take (S n) (Cons x xs) ≃ Cons x (take n xs)

-- FAIL
-- goal_43 :: (a -> Bool) -> List a -> Equation
-- goal_43 p xs =
--   app (takeWhile p xs) (dropWhile p xs) ≃ xs

-- goal_44 :: a -> List a -> List a -> Equation
-- goal_44 x xs ys =
--   zip (Cons x xs) ys ≃ zipConcat x xs ys

-- goal_45 :: a -> b -> List a -> List b -> Equation
-- goal_45 x y xs ys =
--   zip (Cons x xs) (Cons y ys) ≃ Cons (x, y) (zip xs ys)

-- goal_46 :: List a -> Equation
-- goal_46 xs =
--   zip Nil xs ≃ Nil

-- goal_47 :: Tree a -> Equation
-- goal_47 t =
--   height (mirror t) ≃ height t

-- FAIL
-- goal_49 :: List a -> List a -> Equation
-- goal_49 xs ys =
--   butlast (app xs ys) ≃ butlastConcat xs ys

-- goal_50 :: List a -> Equation
-- goal_50 xs =
--   butlast xs ≃ take (minus (len xs) (S Z)) xs

-- goal_51 :: List a -> a -> Equation
-- goal_51 xs x =
--   butlast (app xs (Cons x Nil)) ≃ xs

-- FAIL
-- goal_52 :: Nat -> List Nat -> Equation
-- goal_52 n xs =
--   count n xs ≃ count n (rev xs)

-- goal_53 :: Nat -> List Nat -> Equation
-- goal_53 n xs =
--   count n (isort xs) ≃ count n xs

goal_54 :: Nat -> Nat -> Equation
goal_54 n m =
  minus (add m n) n ≃ m