module CycleQ.Unique.Unique
  ( -- * Unique
    Unique (..),

    -- * Unique Objects
    HasUnique (..),
    ViaUnique (..),
  )
where

import GHC.Types.Unique qualified as GHC

-- | A unique identifier.
data Unique
  = -- | GHC uniques
    GHC {-# UNPACK #-} !GHC.Unique
  | -- | CycleQ uniques
    CycleQ {-# UNPACK #-} !Int
  deriving stock (Eq)

-- | CycleQ uniques are dominated by GHC uniques
-- and CycleQ uniques are reverse chronological.
instance Ord Unique where
  compare (GHC n) (GHC m) =
    compare (GHC.getKey n) (GHC.getKey m)
  compare (GHC n) (CycleQ m) = GT
  compare (CycleQ n) (GHC m) = LT
  compare (CycleQ n) (CycleQ m) = compare m n

instance Show Unique where
  show (CycleQ n) = show n
  show (GHC n) = show n

-- * Unique Objects

-- | Uniquely identifiable objects.
class HasUnique a where
  getUnique :: a -> Unique

  setUnique :: a -> Unique -> a

-- | Uniquely identifiable object wrapped for deriving equality and comparison.
newtype ViaUnique a
  = ViaUnique a
  deriving newtype (HasUnique)

instance HasUnique a => Eq (ViaUnique a) where
  ViaUnique a == ViaUnique b =
    getUnique a == getUnique b

instance HasUnique a => Ord (ViaUnique a) where
  compare (ViaUnique a) (ViaUnique b) =
    compare (getUnique a) (getUnique b)
