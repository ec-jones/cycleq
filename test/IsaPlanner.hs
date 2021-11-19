-- Property from "Case-Analysis for Rippling and Inductive Proof",
-- Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010
-- https://github.com/tip-org/benchmarks/blob/master/original/isaplanner/Properties.hs

module Properties where

import Cycleq
import Prelude (Bool(..))

prop_01 :: Nat -> List a -> Equation
prop_01 n xs =
  take n xs ++ drop n xs === xs

-- FAIL
-- prop_02 :: Nat -> List Nat -> List Nat -> Equation
-- prop_02 n xs ys =
--   count n xs + count n ys === count n (xs ++ ys)

-- FAIL
-- prop_03 :: Nat -> List Nat -> List Nat -> Equation
-- prop_03 n xs ys =
--   count n xs <= count n (xs ++ ys) === True

-- FAIL
-- prop_04 :: Nat -> List Nat -> Equation
-- prop_04 n xs =
--   S (count n xs) === count n (Cons n xs)

-- prop_05 n x xs
--   = n === x ==> S (count n xs) === count n (x : xs)

prop_06 :: Nat -> Nat -> Equation
prop_06 n m =
  n - (n + m) === Z

prop_07 :: Nat -> Nat -> Equation
prop_07 n m =
  (n + m) - n === m

prop_08 :: Nat -> Nat -> Nat -> Equation
prop_08 k m n =
  (k + m) - (k + n) === m - n

prop_09 :: Nat -> Nat -> Nat -> Equation
prop_09 i j k =
  (i - j) - k === i - (j + k)

prop_10 :: Nat -> Equation
prop_10 m =
  m - m === Z

prop_11 :: List a -> Equation
prop_11 xs =
  drop Z xs === xs

prop_12 :: Nat -> (a -> b) -> List a -> Equation
prop_12 n f xs =
  drop n (map f xs) === map f (drop n xs)

prop_13 :: Nat -> a -> List a -> Equation
prop_13 n x xs =
  drop (S n) (Cons x xs) === drop n xs

-- FAIL
-- prop_14 :: (a -> Bool) -> List a -> List a -> Equation
-- prop_14 p xs ys =
--   filter p (xs ++ ys) === filter p xs ++ filter p ys

-- FAIL
-- prop_15 :: Nat -> List Nat -> Equation
-- prop_15 x xs =
--   len (ins x xs) === S (len xs)

-- prop_16 :: Nat -> List Nat -> Equation
-- prop_16 x xs
--   = xs === Nil ==> last (Cons x xs) === x

prop_17 :: Nat -> Equation
prop_17 n =
  n <= Z === n == Z

prop_18 :: Nat -> Nat -> Equation
prop_18 i m =
  i < S (i + m) === True

prop_19 :: Nat -> List a -> Equation
prop_19 n xs =
  len (drop n xs) === len xs - n

-- This property is the same as prod #48
-- FAIL
-- prop_20 :: List Nat -> Equation
-- prop_20 xs =
--   len (sort xs) === len xs

prop_21 :: Nat -> Nat -> Equation
prop_21 n m =
  n <= (n + m) === True

prop_22 :: Nat -> Nat -> Nat -> Equation
prop_22 a b c =
  max (max a b) c === max a (max b c)

prop_23 :: Nat -> Nat -> Equation
prop_23 a b =
  max a b === max b a

-- FAIl
-- prop_24 :: Nat -> Nat -> Equation
-- prop_24 a b =
--   max a b == a === b <= a

prop_25 :: Nat -> Nat -> Equation
prop_25 a b =
  max a b == b === a <= b

-- prop_26 x xs ys
--   = x `elem` xs ==> x `elem` (xs ++ ys)

-- prop_27 x xs ys
--   = x `elem` ys ==> x `elem` (xs ++ ys)

-- FAIL
-- prop_28 :: Nat -> List Nat -> Equation
-- prop_28 x xs =
--   x `elem` (xs ++ Cons x Nil) === True

-- FAIL
-- prop_29 :: Nat -> List Nat -> Equation
-- prop_29 x xs =
--   x `elem` ins1 x xs === True

-- FAIL
-- prop_30 :: Nat -> List Nat -> Equation
-- prop_30 x xs =
--   x `elem` ins x xs === True

prop_31 :: Nat -> Nat -> Nat -> Equation
prop_31 a b c =
  min (min a b) c === min a (min b c)

prop_32 :: Nat -> Nat -> Equation
prop_32 a b =
  min a b === min b a

-- FAIL
-- prop_33 :: Nat -> Nat -> Equation
-- prop_33 a b =
--   min a b == a === a <= b

-- FAIL
-- prop_34 :: Nat -> Nat -> Equation
-- prop_34 a b =
--   min a b == b === b <= a

prop_35 :: List a -> Equation
prop_35 xs =
  dropWhile (\_ -> False) xs === xs

prop_36 :: List a -> Equation
prop_36 xs =
  takeWhile (\_ -> True) xs === xs

-- FAIL
-- prop_37 :: Nat -> List Nat -> Equation
-- prop_37 x xs =
--   not (x `elem` delete x xs) === True

-- FAIL
-- prop_38 :: Nat -> List Nat -> Equation
-- prop_38 n xs =
--   count n (xs ++ Cons n Nil) === S (count n xs)

-- FAIL
-- prop_39 :: Nat -> Nat -> List Nat -> Equation
-- prop_39 n x xs =
--   count n (Cons x Nil) + count n xs === count n (Cons x xs)

prop_40 :: List a -> Equation
prop_40 xs =
  take Z xs === Nil

prop_41 :: Nat -> (a -> b) -> List a -> Equation
prop_41 n f xs =
  take n (map f xs) === map f (take n xs)

prop_42 :: Nat -> a -> List a -> Equation
prop_42 n x xs =
  take (S n) (Cons x xs) === Cons x (take n xs)

-- FAIL
-- prop_43 :: (a -> Bool) -> List a -> Equation
-- prop_43 p xs =
--   takeWhile p xs ++ dropWhile p xs === xs

prop_44 :: a -> List a -> List a -> Equation
prop_44 x xs ys =
  zip (Cons x xs) ys === zipConcat x xs ys

prop_45 :: a -> b -> List a -> List b -> Equation
prop_45 x y xs ys =
  zip (Cons x xs) (Cons y ys) === Cons (x, y) (zip xs ys)

prop_46 :: List a -> Equation
prop_46 xs =
  zip Nil xs === Nil

-- FAIL
-- prop_47 :: Tree a -> Equation
-- prop_47 a =
--   height (mirror a) === height a

-- prop_48 :: List a -> Equation
-- prop_48 xs
--   = not (null xs) ==> butlast xs ++ [last xs] === xs

prop_49 :: List a -> List a -> Equation
prop_49 xs ys =
  butlast (xs ++ ys) === butlastConcat xs ys

prop_50 :: List a -> Equation
prop_50 xs =
  butlast xs === take (len xs - S Z) xs

prop_51 :: List a -> a -> Equation
prop_51 xs x =
  butlast (xs ++ Cons x Nil) === xs

-- FAIL
-- prop_52 :: Nat -> List Nat -> Equation
-- prop_52 n xs =
--   count n xs === count n (rev xs)

-- This property is the same as prod #50
-- FAIL
-- prop_53 :: Nat -> List Nat -> Equation
-- prop_53 n xs =
--   count n xs === count n (sort xs)

-- FAIl
-- prop_54 :: Nat -> Nat -> Equation
-- prop_54 n m =
--   (m + n) - n === m

prop_55 :: Nat -> List a -> List a -> Equation
prop_55 n xs ys =
  drop n (xs ++ ys) === drop n xs ++ drop (n - len xs) ys

prop_56 :: Nat -> Nat -> List a -> Equation
prop_56 n m xs =
  drop n (drop m xs) === drop (n + m) xs

prop_57 :: Nat -> Nat -> List a -> Equation
prop_57 n m xs =
  drop n (take m xs) === take (m - n) (drop n xs)

prop_58 :: Nat -> List a -> List a -> Equation
prop_58 n xs ys =
  drop n (zip xs ys) === zip (drop n xs) (drop n ys)

-- prop_59 :: List a -> List a -> Equation
-- prop_59 xs ys
--   = ys === Nil ==> last (xs ++ ys) === last xs

-- prop_60 :: List a -> List a -> Equation
-- prop_60 xs ys
--   = not (null ys) ==> last (xs ++ ys) === last ys

prop_61 :: List Nat -> List Nat -> Equation
prop_61 xs ys =
  last (xs ++ ys) === lastOfTwo xs ys

-- prop_62 xs x
--   = not (null xs) ==> last (Cons x xs) === last xs

-- prop_63 :: Nat -> List a -> Equation
-- prop_63 n xs
--   = n < len xs ==> last (drop n xs) === last xs

prop_64 :: Nat -> List Nat -> Equation
prop_64 x xs =
  last (xs ++ Cons x Nil) === x

prop_65 :: Nat -> Nat -> Equation
prop_65 i m =
  i < S (m + i) === True

-- FAIL
-- prop_66 :: (a -> Bool) -> List a -> Equation
-- prop_66 p xs =
--   len (filter p xs) <= len xs === True

prop_67 :: List a -> Equation
prop_67 xs =
  len (butlast xs) === len xs - S Z

-- FAIL
-- prop_68 :: Nat -> List Nat -> Equation
-- prop_68 n xs =
--   len (delete n xs) <= len xs === True

prop_69 :: Nat -> Nat -> Equation
prop_69 n m =
  n <= (m + n) === True

-- prop_70 m n
--   = m <= n ==> bool (m <= S n)

-- prop_71 :: Nat -> List a-> Equation
-- prop_71 x y xs
--   = (x == y) === False ==> elem x (ins y xs) === elem x xs

-- FAIL
-- prop_72 :: Nat -> List a -> Equation
-- prop_72 i xs =
--   rev (drop i xs) === take (len xs - i) (rev xs)

-- FAIL
-- prop_73 :: (a -> Bool) -> List a -> Equation
-- prop_73 p xs =
--   rev (filter p xs) === filter p (rev xs)

-- FAIL
-- prop_74 :: Nat -> List a -> Equation
-- prop_74 i xs =
--   rev (take i xs) === drop (len xs - i) (rev xs)

-- FAIL
-- prop_75 :: Nat -> Nat -> List Nat -> Equation
-- prop_75 n m xs =
--   count n xs + count n (Cons m Nil) === count n (Cons m xs)

-- prop_76 :: Nat -> Nat -> List Nat -> Equation
-- prop_76 n m xs
--   = (n == m) === False ==> count n (xs ++ Cons m Nil) === count n xs

-- prop_77 x xs
--   = sorted xs ==> sorted (insort x xs)

-- This property is the same as prod #14
-- FAIL
-- prop_78 :: List Nat -> Equation
-- prop_78 xs =
--   sorted (sort xs) === True

prop_79 :: Nat -> Nat -> Nat -> Equation
prop_79 m n k =
  (S m - n) - S k === (m - n) - k

prop_80 :: Nat -> List a -> List a -> Equation
prop_80 n xs ys =
  take n (xs ++ ys) === take n xs ++ take (n - len xs) ys

prop_81 :: Nat -> Nat -> List a -> Equation
prop_81 n m xs {- ys -} =
  take n (drop m xs) === drop m (take (n + m) xs)

prop_82 :: Nat -> List a -> List a -> Equation
prop_82 n xs ys =
  take n (zip xs ys) === zip (take n xs) (take n ys)

prop_83 :: List a -> List a -> List a -> Equation
prop_83 xs ys zs =
  zip (xs ++ ys) zs
    === zip xs (take (len xs) zs) ++ zip ys (drop (len xs) zs)

prop_84 :: List a -> List a -> List a -> Equation
prop_84 xs ys zs =
  zip xs (ys ++ zs)
    === zip (take (len ys) xs) ys ++ zip (drop (len ys) xs) zs

-- One way to prove this is to first show "Nick's lemma":
-- len xs = len ys ==> zip xs ys ++ zip as bs = zip (xs ++ as) (ys ++ bs)
-- prop_85 xs ys
--   = (len xs === len ys) ==>
--     (zip (rev xs) (rev ys) === rev (zip xs ys))

-- prop_86 x y xs
--   = x < y ==> (elem x (ins y xs) === elem x xs)

----------------------------

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
(==) (S n) (S m) = True
(==) (S _) _ = False

(<=) :: Nat -> Nat -> Bool
Z     <= _     = True
_     <= Z     = False
(S x) <= (S y) = x <= y

(<) :: Nat -> Nat -> Bool
_     < Z     = False
Z     < _     = True
(S x) < (S y) = x < y

(+) :: Nat -> Nat -> Nat
Z     + y = y
(S x) + y = S (x + y)

(-) :: Nat -> Nat -> Nat
Z     - _     = Z
x     - Z     = x
(S x) - (S y) = x - y

min :: Nat -> Nat -> Nat
min Z     _    = Z
min _ Z     = Z
min (S x) (S y) = S (min x y)

max :: Nat -> Nat -> Nat
max Z     y     = y             --
max x     Z     = x
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
  if n == x
    then delete n xs
    else Cons x (delete n xs)

len :: List a -> Nat
len Nil = Z
len (Cons _ xs) = S (len xs)

elem :: Nat -> List Nat -> Bool
elem _ Nil = False
elem n (Cons x xs) =
  if n == x
    then True
    else elem n xs

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
  if x == y
    then S (count x ys)
    else count x ys

map :: (a -> b) -> List a -> List b
map f Nil = Nil
map f (Cons x xs) =
  Cons (f x) (map f xs)

takeWhile :: (a -> Bool) -> List a -> List a
takeWhile _ Nil = Nil
takeWhile p (Cons x xs) =
  if p x
    then Cons x (takeWhile p xs)
    else Nil

dropWhile :: (a -> Bool) -> List a -> List a
dropWhile _ Nil = Nil
dropWhile p (Cons x xs) =
  if p x
    then dropWhile p xs
    else Cons x xs

filter :: (a -> Bool) -> List a -> List a
filter _ Nil = Nil
filter p (Cons x xs) =
  if p x
    then Cons x (filter p xs)
    else filter p xs

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
  if n <= x
    then Cons n (Cons x xs)
    else Cons x (insort n xs)

ins :: Nat -> List Nat -> List Nat
ins n Nil = Cons n Nil
ins n (Cons x xs) =
  if n < x
    then Cons n (Cons x xs)
    else Cons x (ins n xs)

ins1 :: Nat -> List Nat -> List Nat
ins1 n Nil = Cons n Nil
ins1 n (Cons x xs) =
  if n == x
    then Cons x xs
    else Cons x (ins1 n xs)

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
