{-# LANGUAGE DerivingStrategies #-}

module SizeChange
  ( Edge (..),
    identityEdge,
    narrowingEdge,
    substEdge,
    isWellFounded,
    unionEdges,
    subsumeEdge,
  )
where

import qualified Data.Foldable as Foldable
import qualified GHC.Arr as Array
import GHC.Plugins hiding (freeVars, (<>))
import Syntax

-- * Proof Edges

-- | A collection of size-change graphs between the same nodes.
data Edge = Edge
  { edgeSCGs :: [SCG],
    edgeLabel :: Maybe SDoc
  }

instance Semigroup Edge where
  edge1 <> edge2 =
    Edge
      { edgeSCGs = [scg1 <> scg2 | scg1 <- edgeSCGs edge1, scg2 <- edgeSCGs edge2],
        edgeLabel = Nothing
      }

-- | An identity edge where shared variables haven't changed.
identityEdge :: Sequent -> Sequent -> Edge
identityEdge sequent1 sequent2 =
  let entries =
        [ ((i, j), Equal)
          | (x, i) <- zip (freeVars sequent1) [0 ..],
            (y, j) <- zip (freeVars sequent2) [0 ..],
            x == y
        ]
   in Edge [mkSCG n m entries] (Just (text ""))
  where
    n = length (freeVars sequent1)
    m = length (freeVars sequent2)

-- | An edge that results from narrowing a variable to a constructor.
narrowingEdge :: Var -> [Var] -> Sequent -> Sequent -> Edge
narrowingEdge x ys sequent1 sequent2 =
  let entries =
        [ ((i, j), mkDecrease z y)
          | (z, i) <- zip (freeVars sequent1) [0 ..],
            (y, j) <- zip (freeVars sequent2) [0 ..]
        ]
      label = pprWithCommas (\y -> ppr y <+> text "<" <+> ppr x) ys
   in Edge [mkSCG n m entries] (Just label)
  where
    n = length (freeVars sequent1)
    m = length (freeVars sequent2)

    mkDecrease z y
      | z == x && elem y ys = Decrease
      | z == y = Equal
      | otherwise = Unknown

-- | An edge that results from superposition.
-- N.B. The subsitution goes in the other direction from the edge.
substEdge :: Subst -> Sequent -> Sequent -> Edge
substEdge (Subst _ subst _ _) sequent1 sequent2 =
  let entries =
        [ ((i, j), mkDecrease z y)
          | (z, i) <- zip (freeVars sequent1) [0 ..],
            (y, j) <- zip (freeVars sequent2) [0 ..]
        ]
      labels =
        [ ppr z <+> text "=" <+> ppr y
          | z <- freeVars sequent1,
            y <- freeVars sequent2,
            Just (Var x) <- pure (lookupVarEnv subst z),
            x == y
        ]
   in Edge [mkSCG n m entries] (Just (interpp'SP labels))
  where
    n = length (freeVars sequent1)
    m = length (freeVars sequent2)

    mkDecrease z y =
      case lookupVarEnv subst y of
        Just (Var x)
          | x == z -> Equal
        _ -> Unknown
-- | Union two sets of size-change graphs.
-- The first argument's label is used.
unionEdges :: Edge -> Edge -> Edge
unionEdges edge1 edge2 =
  Edge
    { edgeSCGs = Foldable.foldl' insert (edgeSCGs edge1) (edgeSCGs edge2),
      edgeLabel = edgeLabel edge1
    }

-- | Add a size-change graph to a set if it is not subsumed.
insert :: [SCG] -> SCG -> [SCG]
insert [] graph = [graph]
insert (graph : graphs) graph'
  | subsumeSCG graph graph' = graph' : graphs
  | subsumeSCG graph' graph = insert graphs graph'
  | otherwise = graph : insert graphs graph'

-- | Check that every size-change graph in the first edge
-- is subsumed by a size-change graph in the second.
subsumeEdge :: Edge -> Edge -> Bool
subsumeEdge edge1 edge2 = 
  all (\scg1 -> any (subsumeSCG scg1) (edgeSCGs edge2)) (edgeSCGs edge1)

-- | Check that an edge is well-founded.
isWellFounded :: Edge -> Bool
isWellFounded = all isSCGWellFounded . edgeSCGs

-- * Size-Change Graphs

-- | An individual size-change graph.
newtype SCG = SCG (Array.Array (Int, Int) Decrease)

instance Semigroup SCG where
  SCG graph1 <> SCG graph2
    | n == n' =
      SCG $
        Array.array
          ((0, 0), (m, p))
          [ ( (i, j),
              maximum [graph1 Array.! (i, k) <> graph2 Array.! (k, j) | k <- Array.range (0, n)]
            )
            | (i, j) <- Array.range ((0, 0), (m, p))
          ]
    | otherwise = pprPanic "Incompatible size-change graph dimensions!" (ppr (n, n'))
    where
      (_, (m, n)) = Array.bounds graph1
      (_, (n', p)) = Array.bounds graph2

-- | Make a size-change graph from a list of entries.
-- Unspecified entries default to 'Unknown'.
mkSCG :: Int -> Int -> [((Int, Int), Decrease)] -> SCG
mkSCG n m = SCG . Array.accumArray max Unknown ((0, 0), (n, m))

-- | Check if any diagonal entry is a decrease.
isSCGWellFounded :: SCG -> Bool
isSCGWellFounded (SCG graph)
  | n /= n' = pprPanic "matrix is not square!" (ppr (n, n'))
  | otherwise = any (\((i, j), d) -> Decrease == d && i == j) (Array.assocs graph)
  where
    (_, (n, n')) = Array.bounds graph

-- | Check if every entry in a size-change graph matrix is more defined than another.
subsumeSCG :: SCG -> SCG -> Bool
subsumeSCG (SCG graph1) (SCG graph2)
  | n /= m = pprPanic "dimension mismatch!" (ppr (n, m))
  | otherwise = all (\ij -> graph1 Array.! ij >= graph2 Array.! ij) (Array.range ((0, 0), n))
  where
    (_, n) = Array.bounds graph1
    (_, m) = Array.bounds graph2

-- * Decreases

-- | The possible relationships between variables.
data Decrease
  = -- | No known relationship.
    Unknown
  | -- | Target is known to be smaller or equal to the source.
    Equal
  | -- | Target is known to be smaller than the source.
    Decrease
  deriving stock (Eq, Ord)

instance Semigroup Decrease where
  Unknown <> _ = Unknown
  _ <> Unknown = Unknown
  Equal <> a = a
  a <> Equal = a
  Decrease <> Decrease = Decrease
