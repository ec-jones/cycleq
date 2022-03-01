-- |
-- Module: Cycleq.Proof
module CycleQ.Proof
  ( Proof (proofWellFounded),
    emptyProof,
    lookupNode,
    insertNode,
    insertEdge,
    drawProof,
  )
where

import CycleQ.Edge
import CycleQ.Equation
import Data.GraphViz
import Data.GraphViz.Attributes.Complete
import qualified Data.IntMap as IntMap
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.IO as Text
import GHC.Data.Maybe
import GHC.Plugins hiding (empty)
import System.IO
import System.Process

-- * Proof graphs

-- | A partially completed preproof graph.
data Proof = Proof
  { -- | Nodes in proof graph
    proofNodes :: IntMap.IntMap Equation,
    -- | Adjacency map of proof graph
    proofEdges :: IntMap.IntMap (IntMap.IntMap Edge),
    -- | Is the proof valid?
    proofWellFounded :: !Bool
  }

-- | Initial empty proof.
emptyProof :: Proof
emptyProof = Proof IntMap.empty IntMap.empty True

-- | Lookup equation from node id.
lookupNode :: Int -> Proof -> Equation
lookupNode i proof =
  case IntMap.lookup i (proofNodes proof) of
    Nothing -> pprPanic "Node could not be found!" (ppr i)
    Just equation -> equation

-- | Insert an unjustified equation into a proof and return the new node's id.
insertNode :: Equation -> Proof -> (Proof, Int)
insertNode equation proof =
  let nextId =
        case IntMap.lookupMax (proofNodes proof) of
          Nothing -> 0
          Just (n, _) -> n + 1
      proof' =
        proof
          { proofNodes = IntMap.insert nextId equation (proofNodes proof)
          }
   in (proof', nextId)

-- | Insert an edge into a proof and close the size-change graphs.
insertEdge :: Int -> Int -> Edge -> Proof -> Proof
insertEdge source target edge proof
  | not (proofWellFounded proof) = proof
  | source == target, not (isWellFounded edge) = proof {proofWellFounded = False}
  | otherwise =
    case IntMap.lookup source (proofEdges proof) >>= IntMap.lookup target of
      Nothing ->
        close $ proof {proofEdges = insertEdgeUnclosed edge}
      Just edge'
        | edge `isAsStrongAsEdge` edge' ->
          proof {proofEdges = insertEdgeUnclosed (edge' {edgeLabel = edgeLabel edge `firstJust` edgeLabel edge'})}
        | edge' `isAsStrongAsEdge` edge ->
          close $ proof {proofEdges = insertEdgeUnclosed (edge {edgeLabel = edgeLabel edge `firstJust` edgeLabel edge'})}
        | otherwise -> close $ proof {proofEdges = insertEdgeUnclosed (unionEdges edge edge')}
  where
    insertEdgeUnclosed :: Edge -> IntMap.IntMap (IntMap.IntMap Edge)
    insertEdgeUnclosed edge' =
      IntMap.alter (Just . IntMap.insert target edge' . fromMaybe IntMap.empty) source (proofEdges proof)

    close :: Proof -> Proof
    close proof' =
      let edges = proofEdges proof'
          succs = fromMaybe IntMap.empty (IntMap.lookup target edges)
          preds = IntMap.mapMaybe (IntMap.lookup source) edges
          proof'' = IntMap.foldrWithKey (\node edge' -> insertEdge source node (edge Prelude.<> edge')) proof' succs
       in IntMap.foldrWithKey (\node edge' -> insertEdge node target (edge' Prelude.<> edge)) proof'' preds

-- | Write a proof out as SVG using the @dot@ system command.
drawProof :: Proof -> FilePath -> CoreM ()
drawProof proof path = do
  dynFlags <- getDynFlags
  let ns = IntMap.toList (proofNodes proof)
      es =
        [ (m, n, l)
          | (n, ss) <- IntMap.toList (proofEdges proof),
            (m, cs) <- IntMap.toList ss,
            Just l <- pure (edgeLabel cs)
        ]
  liftIO $
    withFile path WriteMode $ \hout -> do
      (Just hin, _, _, _) <-
        createProcess $
          (proc "dot" ["-Tsvg"])
            { std_in = CreatePipe,
              std_out = UseHandle hout
            }
      Text.hPutStr hin (printDotGraph $ graphElemsToDot (params dynFlags) ns es)
  where
    params :: DynFlags -> GraphvizParams Int Equation SDoc () Equation
    params dynFlags =
      nonClusteredParams
        { globalAttributes =
            [ NodeAttrs [FontName (Text.pack "courier")],
              EdgeAttrs [FontName (Text.pack "courier")]
            ],
          fmtNode = \(i, n) ->
            [ textLabel (Text.pack (showSDoc dynFlags (ppr i GHC.Plugins.<> text ":" <+> ppr n)))
            ],
          fmtEdge = \(_, _, l) -> [textLabel (Text.pack (showSDoc dynFlags l))]
        }
