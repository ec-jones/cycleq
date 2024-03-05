module CycleQ.Proof.Edge
  ( -- * Edges
    Edge (edgeLabel),
    union,
    plus,
    withLabel,
    subsumedBy,
    wellFounded,

    -- * Smart Constructors
    emptyEdge,
    identityEdge,
    caseEdge,
    substEdge,
  )
where

import Control.Applicative ((<|>))
import CycleQ.Syntax
import Data.Map qualified as Map
import Data.Map.Merge.Lazy qualified as Map
import Data.Monoid

-- | A collection of size-change graphs.
data Edge = Edge
  { -- | Pair-wise incomparable size-change graphs.
    sizeChanges :: [SizeChange],
    -- | The label of an edge.
    edgeLabel :: Maybe String
  }

-- | Sequential composition of edges.
instance Semigroup Edge where
  edge <> edge' =
    Edge {sizeChanges = scs, edgeLabel = Nothing}
    where
      scs :: [SizeChange]
      scs =
        foldr
          ( \sc acc ->
              foldr (\sc' -> insertSizeChange (sc <> sc')) acc (sizeChanges edge')
          )
          []
          (sizeChanges edge)

-- | Union two edges.
union :: Edge -> Edge -> Edge
union edge edge' =
  edge
    { sizeChanges =
        foldr insertSizeChange (sizeChanges edge) (sizeChanges edge'),
      edgeLabel = edgeLabel edge <|> edgeLabel edge'
    }

-- | Kleene one-or-more iteration of an edge.
plus :: Edge -> Edge
plus edge =
  let edge2 = edge <> edge
   in if edge2 `subsumedBy` edge
        then edge
        else plus (edge2 `union` edge)

-- | Set the label of an edge if it doesn't already have one.
withLabel :: Edge -> Maybe String -> Edge
withLabel edge label =
  edge
    { edgeLabel = edgeLabel edge <|> label
    }

-- | An edge is subsumed if it only contains size-change graphs that are better or equal.
subsumedBy :: Edge -> Edge -> Bool
subsumedBy edge edge' =
  all
    ( \sc ->
        case dominates sc (sizeChanges edge') of
          DominatedBy _ -> True -- There already exist a size-change graph that is worse or equal.
          Dominates _ _ -> False
    )
    (sizeChanges edge)

-- | Check if an edge is well-founded.
wellFounded :: Edge -> Bool
wellFounded =
  all wellFoundedSizeChange 
    . filter isIdempotent
    . sizeChanges

-- * Smart constructors

-- | Edge with no size-change graphs.
emptyEdge :: Edge
emptyEdge = Edge {sizeChanges = [], edgeLabel = Nothing}

-- | Create an identity edge for the given set of variables.
identityEdge :: [Var] -> String -> Edge
identityEdge xs label =
  let sc = Map.fromList [(x, Map.singleton x False) | x <- xs]
   in Edge
        { sizeChanges = [mkSizeChange sc],
          edgeLabel = Just label
        }

-- | An edge that results from narrowing an expression to a constructor.
caseEdge :: [Var] -> Expr -> Expr -> [Var] -> Edge
caseEdge xs subject result ys
  | Var z [] <- subject,
    z `elem` xs =
      let sc =
            Map.insert z (Map.fromList [(y, True) | y <- ys]) $
              Map.fromList [(x, Map.singleton x False) | x <- xs]
       in Edge
            { sizeChanges = [mkSizeChange sc],
              edgeLabel = Just (showPairs [(subject, result)])
            }
  | otherwise =
      identityEdge xs (showPairs [(subject, result)])

-- | Create a substitution edge.
substEdge :: [Var] -> Subst -> Edge
substEdge xs theta =
  let sc =
        Map.fromList
          [ ( x,
              Map.mapMaybe
                ( \case
                    Var x' []
                      | x == x' -> Just False
                    noMatch -> Nothing
                )
                theta
            )
            | x <- xs
          ]
      label = showPairs (Map.toList theta)
   in Edge
        { sizeChanges = [mkSizeChange sc],
          edgeLabel = Just label
        }

showPairs :: forall a b. (Show a, Show b) => [(a, b)] -> String
showPairs subst = "{ " ++ foldr go "}" subst
  where
    go :: (a, b) -> String -> String
    go (lhs, rhs) k =
      show lhs ++ " -> " ++ show rhs ++ "; " ++ k

-- * Size-Change Graphs

-- | A size-change graph.
newtype SizeChange
  = SizeChange
      ( Map.Map
          Var
          (Map.Map Var Bool) -- Cannot be empty
      )
  deriving newtype (Eq)

-- | Sequential composition of size-change graphs.
instance Semigroup SizeChange where
  SizeChange m <> SizeChange m' =
    mkSizeChange $ fmap (Map.foldrWithKey go Map.empty) m
    where
      go :: Var -> Bool -> Map.Map Var Bool -> Map.Map Var Bool
      go y p acc =
        case Map.lookup y m' of
          Nothing -> acc
          Just zs ->
            Map.unionWith (||) (fmap (|| p) zs) acc

-- | Ensure size-change graph invariant holds.
mkSizeChange :: Map.Map Var (Map.Map Var Bool) -> SizeChange
mkSizeChange =
  SizeChange . Map.filter (not . Map.null)

-- | Check if a size-change graph has a progress point.
wellFoundedSizeChange :: SizeChange -> Bool
wellFoundedSizeChange sc@(SizeChange m) = 
  case compareSizeChange (sc <> sc) sc of
    Nothing -> True -- Not idempotent
    Just LT -> True -- Not idempotent
    idempotent ->
      -- Check graph has decreasing edge
      getAny $
        Map.foldMapWithKey
          ( \x ys ->
              case Map.lookup x ys of
                Nothing -> Any False
                Just p -> Any p
          )
          m

-- | Insert a size-change graph into a list.
-- This function removes dominated size-changes, i.e. those with less or weaker edges.
insertSizeChange :: SizeChange -> [SizeChange] -> [SizeChange]
insertSizeChange sc scs =
  case dominates sc scs of
    DominatedBy _ -> scs -- There already exists a size-change graph that is worse or equal.
    Dominates _ scs' -> sc : scs' -- Remove better size-change graphs.

-- | Check if a size-change graph is idempotent.
isIdempotent :: SizeChange -> Bool
isIdempotent sz = sz == sz <> sz

-- ** Size-change graph comparison.

-- | A summary of size-change graphs that are worse, unrelated, or better.
data Comparison
  = DominatedBy
      SizeChange -- \^ A size-change graph that is worse or equal.
  | Dominates
      [SizeChange] -- \^ Better size-change graphs
      [SizeChange] -- \^ Unrelated size-change graphs

-- | Partition a collection of size-change graphs by comparison.
dominates :: SizeChange -> [SizeChange] -> Comparison
dominates x = foldr go (Dominates [] [])
  where
    go :: SizeChange -> Comparison -> Comparison
    go y (DominatedBy z) = DominatedBy z
    go y (Dominates ys zs) =
      case compareSizeChange x y of
        Nothing -> Dominates ys (y : zs)
        Just LT -> Dominates (y : ys) zs
        Just EQ -> DominatedBy y
        Just GT -> DominatedBy y

-- | Comparison of size-change graphs where better graphs have more or stronger edges.
compareSizeChange :: SizeChange -> SizeChange -> Maybe Ordering
compareSizeChange (SizeChange sc) (SizeChange sc') =
  compareMaps
    ( compareMaps
        (\x y -> Just (compare x y)) -- Better graphs have stronger edges
    )
    sc
    sc'

-- GT is "better", i.e. more or better edges 
-- False <= True, i.e. equal is "worse" than decrease

compareMaps :: Ord k => (a -> a -> Maybe Ordering) -> Map.Map k a -> Map.Map k a -> Maybe Ordering
compareMaps comp xs ys =
  foldr go (Just EQ) $
    Map.merge
      ( Map.mapMissing $ \_ x -> Just GT -- Better graphs have more edges
      )
      ( Map.mapMissing $ \_ y -> Just LT -- Worse graphs have less edges
      )
      (Map.zipWithMatched $ \_ -> comp)
      xs
      ys
  where
    go :: Maybe Ordering -> Maybe Ordering -> Maybe Ordering
    go Nothing _ = Nothing
    go _ Nothing = Nothing
    go (Just LT) (Just LT) = Just LT
    go (Just LT) (Just EQ) = Just LT
    go (Just LT) (Just GT) = Nothing
    go (Just EQ) (Just LT) = Just LT
    go (Just EQ) (Just EQ) = Just EQ
    go (Just EQ) (Just GT) = Just GT
    go (Just GT) (Just LT) = Nothing
    go (Just GT) (Just EQ) = Just GT
    go (Just GT) (Just GT) = Just GT
