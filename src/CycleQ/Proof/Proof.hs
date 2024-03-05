module CycleQ.Proof.Proof
  ( -- * Proof
    Proof,
    empty,
    size,
    lookupNode,
    insertNode,
    insertEdge,
    closure,
    drawProof,

    -- * Edges
    Edge,
    identityEdge,
    caseEdge,
    substEdge,
  )
where

import Control.Monad.State
import CycleQ.Proof.Edge
import CycleQ.Syntax
import Data.GraphViz
import Data.GraphViz.Attributes.Complete
import Data.IntMap qualified as IntMap
import Data.Maybe
import Data.Text.Lazy qualified as Text
import System.Process

-- * Proof

-- | A cyclic proof represented as an adjacency map.
data Proof = Proof
  { nextNode :: !Int,
    proofNodes :: !(IntMap.IntMap Clause),
    proofEdges :: !AdjMap
  }

-- | Create an empty proof.
empty :: Proof
empty =
  Proof
    { nextNode = 0,
      proofNodes = IntMap.empty,
      proofEdges = IntMap.empty
    }

-- | The number of prof nodes.
size :: Proof -> Int
size = nextNode

-- | Find the clause associated with a given node.
lookupNode :: Int -> Proof -> Clause
lookupNode n proof =
  case IntMap.lookup n (proofNodes proof) of
    Nothing -> error "Proof node not found!"
    Just clause -> clause

-- | Insert a clause into a proof as a new node.
insertNode :: Clause -> Proof -> (Proof, Int)
insertNode clause proof =
  let node = nextNode proof
   in ( proof
          { nextNode = node + 1,
            proofNodes = IntMap.insert node clause (proofNodes proof)
          },
        node
      )

-- | Insert an edge into a proof graph and compute the transitive closure if online.
-- This function returns @Nothing@ if the proof is not well-founded.
insertEdge :: (?online :: Bool) => Int -> Int -> Edge -> Proof -> Maybe Proof
insertEdge n m edge proof = do
  adjMap <- execStateT (insertEdgeAdjMap n m edge) (proofEdges proof)
  pure proof {proofEdges = adjMap}

-- | Take the transitive closure of a proof graph.
-- This function returns @Nothing@ if the proof is not well-founded.
closure :: (?online :: Bool) => Proof -> Maybe Proof
closure proof
  | ?online = pure proof
  | otherwise = do
      let nodes = IntMap.keys (proofNodes proof)
      adjMap <- execStateT (forM_ nodes $ updateVia nodes) (proofEdges proof)
      pure proof {proofEdges = adjMap}

-- | Display a proof graph as an SVG using the @dot@ system command.
drawProof :: Proof -> FilePath -> IO ()
drawProof proof filePath = do
  let ns = IntMap.toList (proofNodes proof)
      es =
        [ (n, m, l)
          | (n, ms) <- IntMap.toList (proofEdges proof),
            (m, edge) <- IntMap.toList ms,
            Just l <- pure (edgeLabel edge)
        ]
      graph = graphElemsToDot params ns es

  svg <- readProcess "dot" ["-Tsvg"] (Text.unpack (printDotGraph graph))
  writeFile filePath svg
  where
    params :: GraphvizParams Int Clause String () Clause
    params =
      nonClusteredParams
        { globalAttributes =
            [ NodeAttrs [FontName (Text.pack "courier")],
              EdgeAttrs [FontName (Text.pack "courier")]
            ],
          fmtNode = \(n, clause) ->
            [ toLabel (show n ++ ": " ++ show clause)
            ],
          fmtEdge = \(_, _, l) -> [toLabel l]
        }

-- * Adjacency Map

type AdjMap =
  IntMap.IntMap (IntMap.IntMap Edge)

-- | Find the edge between two nodes.
lookupEdge :: Monad m => Int -> Int -> StateT AdjMap m Edge
lookupEdge n m = do
  adjMap <- get
  case IntMap.lookup n adjMap >>= IntMap.lookup m of
    Nothing -> pure emptyEdge
    Just edge -> pure edge

-- | Insert an edge into an adjacency map.
insertEdgeAdjMap :: (?online :: Bool) => Int -> Int -> Edge -> StateT AdjMap Maybe ()
insertEdgeAdjMap n m new
  | ?online, n == m, not (wellFounded new) = lift Nothing
  | otherwise = do
      -- Modify the adjacency map
      adjMap <- get
      let (change, adjMap') =
            IntMap.alterF
              ( fmap Just
                  . IntMap.alterF
                    ( \case
                        Nothing -> (True, Just new)
                        Just old
                          | new `subsumedBy` old ->
                              -- Adding the new edge would not make the graph any worse.
                              (False, Just (old `withLabel` edgeLabel new))
                          | otherwise ->
                              (True, Just (old `union` new))
                    )
                    m
                  . fromMaybe IntMap.empty
              )
              n
              adjMap

      put adjMap'

      -- When online transitively close the proof graph
      when (?online && change) $
        case IntMap.lookup m adjMap' of
          Nothing -> pure ()
          Just succs ->
            forM_ (IntMap.toList succs) $ \(succ, succEdge) ->
              insertEdgeAdjMap n succ (new <> succEdge)

-- | Update paths via the given node, used in offline transitive closure.
updateVia :: (?online :: Bool) => [Int] -> Int -> StateT AdjMap Maybe ()
updateVia nodes k =
  forM_ nodes $ \n -> do
    nk <- lookupEdge n k
    kk <- lookupEdge k k

    let nkk :: Edge
        nkk = nk `union` (nk <> plus kk)

    forM_ nodes $ \m -> do
      km <- lookupEdge k m

      let delta = nkk <> km
      if n == m && not (wellFounded delta)
        then lift Nothing
        else insertEdgeAdjMap n m delta
