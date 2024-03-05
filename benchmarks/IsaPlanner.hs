{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TypeApplications #-}

module IsaPlanner where

import CycleQ
import Prelude ()

-- {-# ANN prop_01 defaultParams { output = "proofs/prop_01.svg" } #-}
-- prop_01 :: Nat -> List a -> Formula
-- prop_01 n xs =
--   take n xs ++ drop n xs === xs

-- -- Conditional
-- {-# ANN prop_02 defaultParams #-}
-- prop_02 :: Nat -> List Nat -> List Nat -> Formula
-- prop_02 n xs ys =
--   count n xs + count n ys === count n (xs ++ ys)

-- -- Conditional
-- {-# ANN prop_03 defaultParams #-}
-- prop_03 :: Nat -> List Nat -> List Nat -> Formula
-- prop_03 n xs ys =
--   count n xs <= count n (xs ++ ys) === True

-- -- Conditional
-- {-# ANN prop_04 defaultParams #-}
-- prop_04 :: Nat -> List Nat -> Formula
-- prop_04 n xs =
--   S (count n xs) === count n (Cons n xs)

-- -- Conditional
-- {-# ANN prop_05 defaultParams #-}
-- prop_05 :: Nat -> Nat -> List Nat -> Formula
-- prop_05 n x xs =
--   n
--     === x
--     ==> S (count n xs)
--     === count n (Cons x xs)

-- {-# ANN prop_06 defaultParams #-}
-- prop_06 :: Nat -> Nat -> Formula
-- prop_06 n m =
--   n - (n + m) === Z

-- {-# ANN prop_07 defaultParams #-}
-- prop_07 :: Nat -> Nat -> Formula
-- prop_07 n m =
--   (n + m) - n === m

-- {-# ANN prop_08 defaultParams #-}
-- prop_08 :: Nat -> Nat -> Nat -> Formula
-- prop_08 k m n =
--   (k + m) - (k + n) === m - n

-- {-# ANN prop_09 defaultParams #-}
-- prop_09 :: Nat -> Nat -> Nat -> Formula
-- prop_09 i j k =
--   (i - j) - k === i - (j + k)

-- {-# ANN prop_10 defaultParams #-}
-- prop_10 :: Nat -> Formula
-- prop_10 m =
--   m - m === Z

-- {-# ANN prop_11 defaultParams #-}
-- prop_11 :: List a -> Formula
-- prop_11 xs =
--   drop Z xs === xs

-- {-# ANN prop_12 defaultParams #-}
-- prop_12 :: Nat -> (a -> b) -> List a -> Formula
-- prop_12 n f xs =
--   drop n (map f xs) === map f (drop n xs)

-- {-# ANN prop_13 defaultParams #-}
-- prop_13 :: Nat -> a -> List a -> Formula
-- prop_13 n x xs =
--   drop (S n) (Cons x xs) === drop n xs

-- -- Conditional
-- {-# ANN prop_14 defaultParams #-}
-- prop_14 :: (a -> Bool) -> List a -> List a -> Formula
-- prop_14 p xs ys =
--   filter p (xs ++ ys) === filter p xs ++ filter p ys

-- -- Conditional
-- {-# ANN prop_15 defaultParams #-}
-- prop_15 :: Nat -> List Nat -> Formula
-- prop_15 x xs =
--   len (ins x xs) === S (len xs)

-- -- Conditional
-- {-# ANN prop_16 defaultParams #-}
-- prop_16 :: Nat -> List Nat -> Formula
-- prop_16 x xs =
--   xs === Nil ==> last (Cons x xs) === x

-- {-# ANN prop_17 defaultParams #-}
-- prop_17 :: Nat -> Formula
-- prop_17 n =
--   n <= Z === n == Z

-- {-# ANN prop_18 defaultParams #-}
-- prop_18 :: Nat -> Nat -> Formula
-- prop_18 i m =
--   i < S (i + m) === True

-- {-# ANN prop_19 defaultParams #-}
-- prop_19 :: Nat -> List a -> Formula
-- prop_19 n xs =
--   len (drop n xs) === len xs - n

-- Lemma & Conditional
{-# ANN prop_20 defaultParams #-}
prop_20 :: List Nat -> Formula
prop_20 xs =
  len (sort xs) === len xs

-- lemma_1 :: Nat -> List Nat -> Formula
-- lemma_1 =
--   len (insort x xs) == len (x : xs)

-- {-# ANN prop_21 defaultParams #-}
-- prop_21 :: Nat -> Nat -> Formula
-- prop_21 n m =
--   n <= (n + m) === True

-- {-# ANN prop_22 defaultParams #-}
-- prop_22 :: Nat -> Nat -> Nat -> Formula
-- prop_22 a b c =
--   max (max a b) c === max a (max b c)

-- {-# ANN prop_23 defaultParams #-}
-- prop_23 :: Nat -> Nat -> Formula
-- prop_23 a b =
--   max a b === max b a

-- {-# ANN prop_24 defaultParams #-}
-- prop_24 :: Nat -> Nat -> Formula
-- prop_24 a b =
--   max a b == a === b <= a

-- {-# ANN prop_25 defaultParams #-}
-- prop_25 :: Nat -> Nat -> Formula
-- prop_25 a b =
--   max a b == b === a <= b

-- -- Conditional
-- {-# ANN prop_26 defaultParams #-}
-- prop_26 x xs ys =
--   x `elem` xs === True ==> x `elem` (xs ++ ys) === True

-- -- Conditional
-- {-# ANN prop_27 defaultParams #-}
-- prop_27 x xs ys =
--   x `elem` ys === True ==> x `elem` (xs ++ ys) === True

-- -- Conditional
-- {-# ANN prop_28 defaultParams #-}
-- prop_28 :: Nat -> List Nat -> Formula
-- prop_28 x xs =
--   x `elem` (xs ++ Cons x Nil) === True

-- -- Conditional
-- {-# ANN prop_29 defaultParams #-}
-- prop_29 :: Nat -> List Nat -> Formula
-- prop_29 x xs =
--   x `elem` ins1 x xs === True

-- -- Conditional
-- {-# ANN prop_30 defaultParams #-}
-- prop_30 :: Nat -> List Nat -> Formula
-- prop_30 x xs =
--   x `elem` ins x xs === True

-- {-# ANN prop_31 defaultParams #-}
-- prop_31 :: Nat -> Nat -> Nat -> Formula
-- prop_31 a b c =
--   min (min a b) c === min a (min b c)

-- {-# ANN prop_32 defaultParams #-}
-- prop_32 :: Nat -> Nat -> Formula
-- prop_32 a b =
--   min a b === min b a

-- {-# ANN prop_33 defaultParams #-}
-- prop_33 :: Nat -> Nat -> Formula
-- prop_33 a b =
--   min a b == a === a <= b

-- {-# ANN prop_34 defaultParams #-}
-- prop_34 :: Nat -> Nat -> Formula
-- prop_34 a b =
--   min a b == b === b <= a

-- {-# ANN prop_35 defaultParams #-}
-- prop_35 :: List a -> Formula
-- prop_35 xs =
--   dropWhile (\_ -> False) xs === xs

-- {-# ANN prop_36 defaultParams #-}
-- prop_36 :: List a -> Formula
-- prop_36 xs =
--   takeWhile (\_ -> True) xs === xs

-- -- Conditional
-- {-# ANN prop_37 defaultParams #-}
-- prop_37 :: Nat -> List Nat -> Formula
-- prop_37 x xs =
--   not (x `elem` delete x xs) === True

-- -- Conditional
-- {-# ANN prop_38 defaultParams #-}
-- prop_38 :: Nat -> List Nat -> Formula
-- prop_38 n xs =
--   count n (xs ++ Cons n Nil) === S (count n xs)

-- -- Conditional
-- {-# ANN prop_39 defaultParams #-}
-- prop_39 :: Nat -> Nat -> List Nat -> Formula
-- prop_39 n x xs =
--   count n (Cons x Nil) + count n xs === count n (Cons x xs)

-- {-# ANN prop_40 defaultParams #-}
-- prop_40 :: List a -> Formula
-- prop_40 xs =
--   take Z xs === Nil

-- {-# ANN prop_41 defaultParams #-}
-- prop_41 :: Nat -> (a -> b) -> List a -> Formula
-- prop_41 n f xs =
--   take n (map f xs) === map f (take n xs)

-- {-# ANN prop_42 defaultParams #-}
-- prop_42 :: Nat -> a -> List a -> Formula
-- prop_42 n x xs =
--   take (S n) (Cons x xs) === Cons x (take n xs)

-- -- Conditional
-- {-# ANN prop_43 defaultParams #-}
-- prop_43 :: (a -> Bool) -> List a -> Formula
-- prop_43 p xs =
--   takeWhile p xs ++ dropWhile p xs === xs

-- {-# ANN prop_44 defaultParams #-}
-- prop_44 :: a -> List a -> List a -> Formula
-- prop_44 x xs ys =
--   zip (Cons x xs) ys === zipConcat x xs ys

-- {-# ANN prop_45 defaultParams #-}
-- prop_45 :: a -> b -> List a -> List b -> Formula
-- prop_45 x y xs ys =
--   zip (Cons x xs) (Cons y ys) === Cons (x, y) (zip xs ys)

-- {-# ANN prop_46 defaultParams #-}
-- prop_46 :: List a -> Formula
-- prop_46 xs =
--   zip @() Nil xs === Nil

-- Lemma
-- {-# ANN
--   prop_47
--   defaultParams
--     { lemmas = ['maxComm]
--     }
--   #-}
-- prop_47 :: Tree a -> Formula
-- prop_47 a =
--   height (mirror a) === height a

-- {-# ANN maxComm assumption #-}
-- maxComm :: Nat -> Nat -> Formula
-- maxComm n m =
--   max n m === max m n

-- Conditional
-- {-# ANN prop_48 defaultParams #-}
-- prop_48 :: List Nat -> Formula
-- prop_48 xs =
--   not (null xs) === True ==> butlast xs ++ Cons (last xs) Nil === xs

-- {-# ANN prop_49 defaultParams #-}
-- prop_49 :: List a -> List a -> Formula
-- prop_49 xs ys =
--   butlast (xs ++ ys) === butlastConcat xs ys

-- {-# ANN prop_50 defaultParams #-}
-- prop_50 :: List a -> Formula
-- prop_50 xs =
--   butlast xs === take (len xs - S Z) xs

-- {-# ANN prop_51 defaultParams #-}
-- prop_51 :: List a -> a -> Formula
-- prop_51 xs x =
--   butlast (xs ++ Cons x Nil) === xs

-- Conditional & Lemma
-- {-# ANN prop_52 defaultParams #-}
-- prop_52 :: Nat -> List Nat -> Formula
-- prop_52 n xs =
--   count n xs === count n (rev xs)

-- Conditional & Lemma
-- {-# ANN prop_53 defaultParams #-}
-- prop_53 :: Nat -> List Nat -> Formula
-- prop_53 n xs =
--   count n xs === count n (sort xs)

-- Lemma
-- {-# ANN prop_54 defaultParams #-}
-- prop_54 :: Nat -> Nat -> Formula
-- prop_54 n m =
--   (m + n) - n === m

-- {-# ANN addComm assumption #-}
-- addComm :: Nat -> Nat -> Formula
-- addComm n m =
--   n + m === m + n

-- {-# ANN prop_55 defaultParams #-}
-- prop_55 :: Nat -> List a -> List a -> Formula
-- prop_55 n xs ys =
--   drop n (xs ++ ys) === drop n xs ++ drop (n - len xs) ys

-- {-# ANN prop_56 defaultParams #-}
-- prop_56 :: Nat -> Nat -> List a -> Formula
-- prop_56 n m xs =
--   drop n (drop m xs) === drop (n + m) xs

-- {-# ANN prop_57 defaultParams #-}
-- prop_57 :: Nat -> Nat -> List a -> Formula
-- prop_57 n m xs =
--   drop n (take m xs) === take (m - n) (drop n xs)

-- {-# ANN prop_58 defaultParams #-}
-- prop_58 :: Nat -> List a -> List a -> Formula
-- prop_58 n xs ys =
--   drop n (zip xs ys) === zip (drop n xs) (drop n ys)

-- -- Conditional
-- {-# ANN prop_59 defaultParams #-}
-- prop_59 :: List Nat -> List Nat -> Formula
-- prop_59 xs ys =
--   ys === Nil ==> last (xs ++ ys) === last xs

-- -- Conditional
-- {-# ANN prop_60 defaultParams #-}
-- prop_60 :: List Nat -> List Nat -> Formula
-- prop_60 xs ys =
--   not (null ys) === True ==> last (xs ++ ys) === last ys

-- {-# ANN prop_61 defaultParams #-}
-- prop_61 :: List Nat -> List Nat -> Formula
-- prop_61 xs ys =
--   last (xs ++ ys) === lastOfTwo xs ys

-- -- Conditional
-- {-# ANN prop_62 defaultParams #-}
-- prop_62 xs x =
--   not (null xs) === True ==> last (Cons x xs) === last xs

-- -- Conditional
-- {-# ANN prop_63 defaultParams #-}
-- prop_63 :: Nat -> List Nat -> Formula
-- prop_63 n xs =
--   n < len xs === True ==> last (drop n xs) === last xs

-- {-# ANN prop_64 defaultParams #-}
-- prop_64 :: Nat -> List Nat -> Formula
-- prop_64 x xs =
--   last (xs ++ Cons x Nil) === x

-- Lemma
-- {-# ANN prop_65 defaultParams  #-}
-- prop_65 :: Nat -> Nat -> Formula
-- prop_65 i m =
--   i < S (m + i) === True

-- Conditional & Lemma
-- {-# ANN prop_66 defaultParams #-}
-- prop_66 :: (a -> Bool) -> List a -> Formula
-- prop_66 p xs =
--   len (filter p xs) <= len xs === True

-- {-# ANN prop_67 defaultParams #-}
-- prop_67 :: List a -> Formula
-- prop_67 xs =
--   len (butlast xs) === len xs - S Z

-- Lemma
-- {-# ANN prop_68 defaultParams #-}
-- prop_68 :: Nat -> List Nat -> Formula
-- prop_68 n xs =
--   len (delete n xs) <= len xs === True

-- Lemma
-- {-# ANN prop_69 defaultParams  #-}
-- prop_69 :: Nat -> Nat -> Formula
-- prop_69 n m =
--   n <= (m + n) === True

-- -- Conditional
-- {-# ANN prop_70 defaultParams #-}
-- prop_70 m n =
--   m <= n === True ==> (m <= S n) === True

-- -- Conditional
-- {-# ANN prop_71 defaultParams #-}
-- prop_71 :: Nat -> Nat -> List Nat -> Formula
-- prop_71 x y xs =
--   (x == y) === False ==> elem x (ins y xs) === elem x xs

-- Lemma
-- {-# ANN prop_72 defaultParams #-}
-- prop_72 :: Nat -> List a -> Formula
-- prop_72 i xs =
--   rev (drop i xs) === take (len xs - i) (rev xs)

-- Conditional & Lemma
-- {-# ANN prop_73 defaultParams #-}
-- prop_73 :: (a -> Bool) -> List a -> Formula
-- prop_73 p xs =
--   rev (filter p xs) === filter p (rev xs)

-- Lemma
-- {-# ANN prop_74 defaultParams #-}
-- prop_74 :: Nat -> List a -> Formula
-- prop_74 i xs =
--   rev (take i xs) === drop (len xs - i) (rev xs)

-- {-# ANN takeDrop assumption #-}
-- takeDrop :: Nat -> List a -> Formula
-- takeDrop n xs =
--   take n xs ++ drop n xs === xs

-- -- Conditional
-- {-# ANN prop_75 defaultParams #-}
-- prop_75 :: Nat -> Nat -> List Nat -> Formula
-- prop_75 n m xs =
--   count n xs + count n (Cons m Nil) === count n (Cons m xs)

-- -- Conditional
-- {-# ANN prop_76 defaultParams #-}
-- prop_76 :: Nat -> Nat -> List Nat -> Formula
-- prop_76 n m xs =
--   (n == m) === False ==> count n (xs ++ Cons m Nil) === count n xs

-- Conditional & Lemma
-- {-# ANN prop_77 defaultParams #-}
-- prop_77 x xs =
--   sorted xs
--     === True
--     ==> sorted (insort x xs)
--     === True

-- Conditional & Lemma
-- {-# ANN prop_78 defaultParams #-}
-- prop_78 :: List Nat -> Formula
-- prop_78 xs =
--   sorted (sort xs) === True

-- {-# ANN prop_79 defaultParams #-}
-- prop_79 :: Nat -> Nat -> Nat -> Formula
-- prop_79 m n k =
--   (S m - n) - S k === (m - n) - k

-- {-# ANN prop_80 defaultParams #-}
-- prop_80 :: Nat -> List a -> List a -> Formula
-- prop_80 n xs ys =
--   take n (xs ++ ys) === take n xs ++ take (n - len xs) ys

-- Lemma
-- {-# ANN prop_81 defaultParams #-}
-- prop_81 :: Nat -> Nat -> List a -> Formula
-- prop_81 n m xs =
--   take n (drop m xs) === drop m (take (n + m) xs)

-- {-# ANN prop_82 defaultParams #-}
-- prop_82 :: Nat -> List a -> List a -> Formula
-- prop_82 n xs ys =
--   take n (zip xs ys) === zip (take n xs) (take n ys)

-- {-# ANN prop_83 defaultParams #-}
-- prop_83 :: List a -> List a -> List a -> Formula
-- prop_83 xs ys zs =
--   zip (xs ++ ys) zs
--     === zip xs (take (len xs) zs)
--     ++ zip ys (drop (len xs) zs)

-- {-# ANN prop_84 defaultParams #-}
-- prop_84 :: List a -> List a -> List a -> Formula
-- prop_84 xs ys zs =
--   zip xs (ys ++ zs)
--     === zip (take (len ys) xs) ys
--     ++ zip (drop (len ys) xs) zs

-- Conditional & Lemma
-- {-# ANN prop_85 defaultParams #-}
-- prop_85 :: List a -> List a -> Formula
-- prop_85 xs ys
--   = (len xs === len ys) ==>
--     (zip (rev xs) (rev ys) === rev (zip xs ys))

----------------------------

data Bool
  = False
  | True

data Nat
  = Z
  | S Nat

data List a
  = Nil
  | Cons a (List a)

data Tree a
  = Leaf
  | Node (Tree a) a (Tree a)

-- Boolean functions

not :: Bool -> Bool
not True = False
not False = True

(&&) :: Bool -> Bool -> Bool
True && True = True
_ && _ = False

-- Natural numbers

(==) :: Nat -> Nat -> Bool
(==) Z Z = True
(==) Z _ = False
(==) (S n) (S m) = n == m
(==) (S _) _ = False

(<=) :: Nat -> Nat -> Bool
Z <= _ = True
_ <= Z = False
(S x) <= (S y) = x <= y

(<) :: Nat -> Nat -> Bool
_ < Z = False
Z < _ = True
(S x) < (S y) = x < y

(+) :: Nat -> Nat -> Nat
Z + y = y
(S x) + y = S (x + y)

(-) :: Nat -> Nat -> Nat
Z - _ = Z
x - Z = x
(S x) - (S y) = x - y

min :: Nat -> Nat -> Nat
min Z _ = Z
min _ Z = Z
min (S x) (S y) = S (min x y)

max :: Nat -> Nat -> Nat
max Z y = y
max x Z = x
max (S x) (S y) = S (max x y)

-- List functions

null :: List a -> Bool
null Nil = True
null _ = False

(++) :: List a -> List a -> List a
Nil ++ ys = ys
(Cons x xs) ++ ys =
  Cons x (xs ++ ys)

rev :: List a -> List a
rev Nil = Nil
rev (Cons x xs) =
  rev xs ++ Cons x Nil

zip :: List a -> List b -> List (a, b)
zip Nil _ = Nil
zip _ Nil = Nil
zip (Cons x xs) (Cons y ys) =
  Cons (x, y) (zip xs ys)

delete :: Nat -> List Nat -> List Nat
delete _ Nil = Nil
delete n (Cons x xs) =
  case n == x of
    True -> delete n xs
    False -> Cons x (delete n xs)

len :: List a -> Nat
len Nil = Z
len (Cons _ xs) = S (len xs)

elem :: Nat -> List Nat -> Bool
elem _ Nil = False
elem n (Cons x xs) =
  case n == x of
    True -> True
    False -> elem n xs

drop :: Nat -> List a -> List a
drop Z xs = xs
drop (S n) Nil = Nil
drop (S n) (Cons x xs) = drop n xs

take :: Nat -> List a -> List a
take Z _ = Nil
take _ Nil = Nil
take (S x) (Cons y ys) = Cons y (take x ys)

count :: Nat -> List Nat -> Nat
count x Nil = Z
count x (Cons y ys) =
  case x == y of
    True -> S (count x ys)
    False -> count x ys

map :: (a -> b) -> List a -> List b
map f Nil = Nil
map f (Cons x xs) =
  Cons (f x) (map f xs)

takeWhile :: (a -> Bool) -> List a -> List a
takeWhile _ Nil = Nil
takeWhile p (Cons x xs) =
  case p x of
    True -> Cons x (takeWhile p xs)
    False -> Nil

dropWhile :: (a -> Bool) -> List a -> List a
dropWhile _ Nil = Nil
dropWhile p (Cons x xs) =
  case p x of
    True -> dropWhile p xs
    False -> Cons x xs

filter :: (a -> Bool) -> List a -> List a
filter _ Nil = Nil
filter p (Cons x xs) =
  case p x of
    True -> Cons x (filter p xs)
    False -> filter p xs

butlast :: List a -> List a
butlast Nil = Nil
butlast (Cons x Nil) = Nil
butlast (Cons x xs) = Cons x (butlast xs)

last :: List Nat -> Nat
last Nil = Z
last (Cons x Nil) = x
last (Cons x xs) = last xs

sorted :: List Nat -> Bool
sorted Nil = True
sorted (Cons x Nil) = True
sorted (Cons x (Cons y ys)) =
  (x <= y) && sorted (Cons y ys)

insort :: Nat -> List Nat -> List Nat
insort n Nil = Cons n Nil
insort n (Cons x xs) =
  case n <= x of
    True -> Cons n (Cons x xs)
    False -> Cons x (insort n xs)

ins :: Nat -> List Nat -> List Nat
ins n Nil = Cons n Nil
ins n (Cons x xs) =
  case n < x of
    True -> Cons n (Cons x xs)
    False -> Cons x (ins n xs)

ins1 :: Nat -> List Nat -> List Nat
ins1 n Nil = Cons n Nil
ins1 n (Cons x xs) =
  case n == x of
    True -> Cons x xs
    False -> Cons x (ins1 n xs)

sort :: List Nat -> List Nat
sort Nil = Nil
sort (Cons x xs) = insort x (sort xs)

butlastConcat :: List a -> List a -> List a
butlastConcat xs Nil = butlast xs
butlastConcat xs ys = xs ++ butlast ys

lastOfTwo :: List Nat -> List Nat -> Nat
lastOfTwo xs Nil = last xs
lastOfTwo _ ys = last ys

zipConcat :: a -> List a -> List b -> List (a, b)
zipConcat _ _ Nil = Nil
zipConcat x xs (Cons y ys) = Cons (x, y) (zip xs ys)

height :: Tree a -> Nat
height Leaf = Z
height (Node l x r) = S (max (height l) (height r))

mirror :: Tree a -> Tree a
mirror Leaf = Leaf
mirror (Node l x r) = Node (mirror r) x (mirror l)
