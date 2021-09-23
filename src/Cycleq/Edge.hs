{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Cycleq.Edge
  ( -- * Edges
    Edge (..),
    identityEdge,
    caseEdge,
    substEdge,
    unionEdges,
    isAsStrongAsEdge,
    isWellFounded,
  )
where

import Control.Applicative
import Cycleq.Equation
import qualified Data.Foldable as Foldable
import qualified GHC.Arr as Array
import GHC.Plugins hiding ((<>))

-- * Proof Edges

-- | An upwards-closed collection of size-change graphs between the same nodes.
data Edge = Edge
  { edgeSCGs :: [SCG],
    edgeLabel :: Maybe SDoc
  }

instance Semigroup Edge where
  Edge {edgeSCGs = scgs1} <> Edge {edgeSCGs = scgs2} =
    let edgeSCGs =
          Foldable.foldl'
            ( \acc scg1 ->
                Foldable.foldl' (\acc' scg2 -> insert acc' (scg1 <> scg2)) acc scgs2
            )
            []
            scgs1
        edgeLabel = Nothing
     in Edge {..}

instance Outputable Edge where
  ppr Edge {edgeSCGs, edgeLabel} =
    text "Edge:"
-- #ifdef DEBUG
--       <+> ppr edgeSCGs
-- #endif
      <+> ppr edgeLabel

-- | An identity edge where shared variables haven't changed.
identityEdge :: Equation -> Equation -> Edge
identityEdge equation1 equation2 =
  let edgeSCGs =
        [ mkSCG
            n
            m
            [ ((i, j), Equal)
              | (x, i) <- zip (equationVars equation1) [0 ..],
                (y, j) <- zip (equationVars equation2) [0 ..],
                x == y
            ]
        ]
      edgeLabel = Just (text "")
   in Edge {..}
  where
    n = length (equationVars equation1) - 1
    m = length (equationVars equation2) - 1

-- | An edge that results from narrowing a variable to a constructor.
caseEdge :: Var -> [Var] -> Equation -> Equation -> Edge
caseEdge x ys equation1 equation2 =
  let edgeSCGs =
        [ mkSCG
            n
            m
            [ ((i, j), mkDecrease z y)
              | (z, i) <- zip (equationVars equation1) [0 ..],
                (y, j) <- zip (equationVars equation2) [0 ..]
            ]
        ]
      edgeLabel = Just (pprWithCommas (\y -> ppr y <+> text "<" <+> ppr x) ys)
   in Edge {..}
  where
    n = length (equationVars equation1) - 1
    m = length (equationVars equation2) - 1

    mkDecrease z y
      | z == x && elem y ys = Decrease
      | z == y = Equal
      | otherwise = Unknown

-- | An edge that results from superposition.
-- N.B. The subsitution goes in the other direction from the edge.
substEdge :: Subst -> Equation -> Equation -> Edge
substEdge (Subst _ subst _ _) equation1 equation2 =
  let edgeSCGs =
        [ mkSCG
            n
            m
            [ ((i, j), mkDecrease z y)
              | (z, i) <- zip (equationVars equation1) [0 ..],
                (y, j) <- zip (equationVars equation2) [0 ..]
            ]
        ]
      edgeLabel =
        Just $
          interpp'SP
            [ ppr z <+> text "=" <+> ppr y
              | z <- equationVars equation1,
                y <- equationVars equation2,
                Just (Var x) <- pure (lookupVarEnv subst z),
                x == y
            ]
   in Edge {..}
  where
    n = length (equationVars equation1) - 1
    m = length (equationVars equation2) - 1

    mkDecrease z y =
      case lookupVarEnv subst y of
        Just (Var x)
          | x == z -> Equal
        _ -> Unknown

-- | Union two sets of size-change graphs.
-- The first argument's label is used.
unionEdges :: Edge -> Edge -> Edge
unionEdges Edge {edgeSCGs = scgs1, edgeLabel = label1} Edge {edgeSCGs = scgs2, edgeLabel = label2} =
  let edgeSCGs = Foldable.foldl' insert scgs1 scgs2
      edgeLabel = label1 <|> label1
   in Edge {..}

-- | Add a size-change graph to a set if it is not subsumed.
insert :: [SCG] -> SCG -> [SCG]
insert [] graph = [graph]
insert (graph : graphs) graph'
  | graph `isAsStrongAsSCG` graph' = insert graphs graph'
  | graph' `isAsStrongAsSCG` graph = graph : graphs
  | otherwise = graph : insert graphs graph'

-- | Check that every size-change graph in the first edge is subsumed by a size-change graph in the second.
isAsStrongAsEdge :: Edge -> Edge -> Bool
isAsStrongAsEdge edge1 edge2 =
  all (\scg1 -> any (isAsStrongAsSCG scg1) (edgeSCGs edge2)) (edgeSCGs edge1)

-- | Check that an edge is well-founded.
isWellFounded :: Edge -> Bool
isWellFounded = all isSCGWellFounded . edgeSCGs

-- * Size-Change Graphs

-- | An individual size-change graph.
newtype SCG = SCG (Array.Array (Int, Int) Decrease)

instance Outputable SCG where
  ppr (SCG arr) = ppr (Array.assocs arr)

instance Semigroup SCG where
  SCG graph1 <> SCG graph2
    | n == n' =
      SCG $
        Array.array
          ((0, 0), (m, p))
          [ ( (i, j),
              let pairs = [graph1 Array.! (i, k) <> graph2 Array.! (k, j) | k <- Array.range (0, n)]
               in if null pairs then Unknown else maximum pairs
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

-- | Check if every entry in a size-change graph matrix is more defined than another.
isAsStrongAsSCG :: SCG -> SCG -> Bool
isAsStrongAsSCG (SCG graph1) (SCG graph2)
  | n /= m = pprPanic "Incompatible size-change graph dimensions!" (ppr (n, m))
  | otherwise = all (\ij -> graph1 Array.! ij >= graph2 Array.! ij) (Array.range ((0, 0), n))
  where
    (_, n) = Array.bounds graph1
    (_, m) = Array.bounds graph2

-- | Check if any diagonal entry is a decrease.
isSCGWellFounded :: SCG -> Bool
isSCGWellFounded (SCG graph)
  | n /= n' = pprPanic "Matrix is not square!" (ppr (n, n'))
  | otherwise = any (\((i, j), d) -> Decrease == d && i == j) (Array.assocs graph)
  where
    (_, (n, n')) = Array.bounds graph

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

instance Outputable Decrease where
  ppr Unknown = text "?"
  ppr Equal = text "<="
  ppr Decrease = text "<"

instance Semigroup Decrease where
  Unknown <> _ = Unknown
  _ <> Unknown = Unknown
  Equal <> a = a
  a <> Equal = a
  Decrease <> Decrease = Decrease

instance Monoid Decrease where
  mempty = Equal
