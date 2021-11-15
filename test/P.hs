module P where

import Prelude ()
import Cycleq

data Bool
  = False
  | True

data Nat
  = Z
  | S Nat

add :: Nat -> Nat -> Nat
add Z n = n
add (S n) m = S (add n m)

double :: Nat -> Nat
double Z = Z
double (S n) = S (S (double n))

even :: Nat -> Bool
even Z = True
even (S n) = odd n

odd :: Nat -> Bool
odd Z = False
odd (S n) = even n

lq :: Nat -> Nat -> Bool
lq Z _ = True
lq (S _) Z = False
lq (S x) (S y) = lq x y

half :: Nat -> Nat
half Z = Z
half (S Z) = S Z
half (S (S n)) = S (half n)

fac :: Nat -> Nat
fac Z = S Z
fac (S n) = mul (S n) (fac n)

mul :: Nat -> Nat -> Nat
mul Z _ = Z
mul (S n) m = add m (mul n m)

itfac :: Nat -> Nat -> Nat
itfac Z y = y
itfac (S n) y = itfac n (mul (S n) y)

itmul :: Nat -> Nat -> Nat -> Nat
itmul Z y z = z
itmul (S x) y z =
  itmul x y (add y z)

exp :: Nat -> Nat -> Nat
exp _ Z = S Z
exp m (S n) = mul m (exp m n) 

itexp :: Nat -> Nat -> Nat -> Nat
itexp x Z z = z
itexp x (S n) z = itexp x n (mul x z)

data List a
  = Nil
  | Cons a (List a)

len :: List a -> Nat
len Nil = Z
len (Cons x xs) = S (len xs)

app :: List a -> List a -> List a
app Nil ys = ys
app (Cons x xs) ys = Cons x (app xs ys)

rev :: List a -> List a
rev Nil = Nil
rev (Cons x xs) = snoc x (rev xs)

revflat :: List (List a) -> List a
revflat Nil = Nil
revflat (Cons x xs) =
  revflat xs `app` rev x

itRev :: List a -> List a -> List a
itRev Nil ys = ys
itRev (Cons x xs) ys = itRev xs (Cons x ys) 

itRevflat :: List (List a) -> List a -> List a
itRevflat Nil ys = ys
itRevflat (Cons x xs) ys =
  itRevflat xs (app (rev x) ys)

snoc :: a -> List a -> List a
snoc x Nil = Cons x Nil
snoc x (Cons y ys) = Cons y (snoc x ys)

drop :: Nat -> List a -> List a
drop Z xs = xs
drop (S n) Nil = Nil 
drop (S n) (Cons x xs) = drop n xs

insert :: Nat -> List Nat -> List Nat
insert n Nil = Cons n Nil
insert n (Cons m xs) =
  case n `lq` m of
    True -> Cons n (Cons m xs)
    False -> Cons m (insert n xs)

isort :: List Nat -> List Nat
isort Nil = Nil
isort (Cons x xs) = insert x (isort xs)

sorted :: List Nat -> Bool
sorted Nil = True
sorted (Cons x Nil) = True
sorted (Cons x (Cons y zs)) =
  case x `lq` y of
    False -> False
    True -> sorted (Cons y zs)
  
rotate :: Nat -> List a -> List a
rotate Z xs = xs
rotate (S n) Nil = Nil
rotate (S n) (Cons x xs) =
  rotate n (snoc x xs)

elem :: Nat -> List Nat -> Bool
elem n Nil = False
elem n (Cons x xs) =
  case n `eq` x of
    True -> True
    False -> elem n xs

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

----------------------------------------------------

-- FAIL
goal_1 :: Nat -> Equation
goal_1 n =
  add n n ≃ double n

-- goal_2 :: List a -> List a -> Equation
-- goal_2 xs ys =
--   len (app xs ys) ≃ len (app ys xs)

-- goal_3 :: List a -> List a -> Equation
-- goal_3 xs ys =
--   len (app xs ys) ≃ add (len ys) (len xs)

-- FAIL
-- goal_4 :: List a -> Equation
-- goal_4 xs =
--   len (app xs xs) ≃ double (len xs)

-- FAIL
-- goal_5 :: List Nat -> Equation
-- goal_5 xs =
--   len (rev xs) ≃ len xs

-- FAIL
-- goal_6 :: List a -> List a -> Equation
-- goal_6 xs ys =
--   len (rev (app xs ys)) ≃ add (len xs) (len ys)

-- goal_7 :: List a -> List a -> Equation
-- goal_7 xs ys =
--   len (itRev xs ys) ≃ add (len xs) (len ys)

-- goal_8 :: Nat -> Nat -> List a -> Equation
-- goal_8 n m xs =
--   drop n (drop m xs) ≃ drop m (drop n xs)

-- goal_9 :: Nat -> Nat -> Nat -> List a -> Equation
-- goal_9 n m k xs =
--   drop n (drop m (drop k xs)) ≃ drop k (drop m (drop n xs))

-- goal_10 :: List a -> Equation
-- goal_10 xs = 
--   rev (rev xs) ≃ xs

-- goal_11 :: List a -> List a -> Equation
-- goal_11 xs ys = 
--   rev (app (rev xs) (rev ys)) ≃ app ys xs

-- goal_12 :: List a -> List a -> Equation
-- goal_12 xs ys =
--   itRev xs ys ≃ app (rev xs) ys

-- FAIL
-- goal_13 :: Nat -> Equation
-- goal_13 n =
--   half (add n n) ≃ n
  
-- goal_14 :: List Nat -> Equation
-- goal_14 xs =
--   sorted (isort xs) ≃ True
  
-- goal_15 :: Nat -> Equation
-- goal_15 n =
--   add n (S n) ≃ S (add n n)
  
-- goal_16 :: Nat -> Equation
-- goal_16 n =
--   even (add n n) ≃ True

-- goal_17 :: List a -> List a -> Equation
-- goal_17 xs ys =
--   rev (rev (app xs ys)) ≃ app (rev (rev xs)) (rev (rev ys))

-- goal_18 :: List a -> List a -> Equation
-- goal_18 xs ys =
--   rev (app (rev xs) ys) ≃ app (rev ys) xs

-- goal_19 :: List a -> List a -> Equation
-- goal_19 xs ys =
--   rev (rev (app xs ys)) ≃ app (rev (rev xs)) ys

-- goal_20 :: List a -> Equation
-- goal_20 xs =
--   even (len (app xs xs)) ≃ True

-- goal_21 :: List a -> List a -> Equation
-- goal_21 xs ys =
--   rotate (len xs) (app xs ys) ≃
--     app ys xs

-- goal_22 :: List a -> List a -> Equation
-- goal_22 xs ys =
--   even (len (app xs ys)) ≃ even (len (app ys xs))

-- goal_23 :: List a -> List a -> Equation
-- goal_23 xs ys =
--   half (len (app xs ys)) ≃ half (len (app ys xs))

-- goal_24 :: Nat -> Nat -> Equation
-- goal_24 n m =
--   even (add n m) ≃ even (add m n)

-- goal_25 :: List a -> List a -> Equation
-- goal_25 xs ys =
--   even (len (app xs ys)) ≃ even (add (len ys) (len xs))

-- goal_26 :: Nat -> Nat -> Equation
-- goal_26 n m =
  -- half (add n m) ≃ half (add m n)

-- goal_27 :: List a -> Equation
-- goal_27 xs =
--   rev xs ≃ itRev xs Nil

-- goal_28 :: List (List a) -> Equation
-- goal_28 xs =
--   revflat xs ≃ itRevflat xs Nil

-- goal_29 :: List a -> Equation
-- goal_29 xs =
--   rev (itRev xs Nil) ≃ xs

-- goal_30 :: List a -> Equation
-- goal_30 xs =
--   rev (app (rev xs) Nil) ≃ xs

-- goal_31 :: List a -> Equation
-- goal_31 xs =
--   itRev (itRev xs Nil) Nil ≃ xs

-- goal_32 :: List a -> Equation
-- goal_32 xs =
--   rotate (len xs) xs ≃ xs

-- goal_33 :: Nat -> Equation
-- goal_33 n =
--   fac n ≃ itfac n (S Z)

-- goal_34 :: Nat -> Nat -> Equation
-- goal_34 n m =
--   mul n m ≃ itmul n m Z

-- goal_35 :: Nat -> Nat -> Equation
-- goal_35 n m =
--   exp n m ≃ itexp n m (S Z)

-- goal_45 :: Nat -> List Nat -> Equation
-- goal_45 n xs =
--   elem n (insert n xs) ≃ True

-- goal_48 :: Nat -> List Nat -> Equation
-- goal_48 n xs =
--   len (isort xs) ≃ len xs

-- goal_50 :: Nat -> List Nat -> Equation
-- goal_50 n xs =
--   count n (isort xs) ≃ count n xs