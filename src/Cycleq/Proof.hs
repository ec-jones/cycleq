{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cycleq.Proof where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Cycleq.Edge
import Cycleq.Equation
import Data.GraphViz
import Data.GraphViz.Attributes.Complete
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.IO as Text
import GHC.Data.Maybe
import GHC.Plugins hiding (empty)
import System.IO
import System.Process

-- | A node in a pre-proof graph
type Node = IntMap.Key

-- | Each node is associated with a map from it's successors to edge weights.
type AdjMap = IntMap.IntMap (IntMap.IntMap Edge)

-- | Modify an edge in an adjacency map.
alterAdjMap :: Functor f => (Maybe Edge -> f Edge) -> Node -> Node -> AdjMap -> f AdjMap
alterAdjMap go source target =
  IntMap.alterF (fmap Just . IntMap.alterF (fmap Just . go) target . fromMaybe IntMap.empty) source

-- | A partial proof graph.
data Proof = Proof
  { proofNodes :: IntMap.IntMap Equation,
    proofEdges :: AdjMap,
    -- | Nodes without a justification
    proofIncompleteNodes :: [Node],
    -- | Nodes suitable for superposition
    proofLemmas :: [Node]
  }

-- | An initial proof with a set of lemmas and no edges.
initProof :: [Equation] -> [Equation] -> Proof
initProof lemmas goals =
  Proof
    { proofNodes = IntMap.fromList (zip [0 ..] (lemmas ++ goals)),
      proofEdges = IntMap.empty,
      proofIncompleteNodes = [length lemmas .. length goals - 1],
      proofLemmas = [0 .. length lemmas - 1]
    }

-- | Insert a equation into a proof and return the new node's index.
insertNode :: MonadState Proof m => Equation -> m Node
insertNode equation = do
  proof <- get
  case IntMap.lookupMax (proofNodes proof) of
    Nothing -> do
      put
        ( proof
            { proofNodes = IntMap.singleton 0 equation,
              proofIncompleteNodes = List.insert 0 (proofIncompleteNodes proof)
            }
        )
      pure 0
    Just (n, _) -> do
      put
        ( proof
            { proofNodes = IntMap.insert (n + 1) equation (proofNodes proof),
              proofIncompleteNodes = List.insert (n + 1) (proofIncompleteNodes proof)
            }
        )
      pure (n + 1)

-- | Mark a node as justified.
markNodeAsJustified :: MonadState Proof m => Node -> m ()
markNodeAsJustified node = modify $
  \proof ->
    proof {proofIncompleteNodes = List.delete node (proofIncompleteNodes proof)}

-- | Mark a node as suitable for superposition.
markNodeAsLemma :: MonadState Proof m => Node -> m ()
markNodeAsLemma node = modify $
  \proof ->
    proof {proofLemmas = List.insert node (proofLemmas proof)}

-- | Get the equation of a given node.
lookupNode :: MonadState Proof m => Node -> m Equation
lookupNode node = do
  proof <- get
  case IntMap.lookup node (proofNodes proof) of
    Nothing -> pprPanic "Node not in graph!" (ppr node)
    Just equation -> return equation

-- | Insert an edge into a proof and returns False if this creates a bad cycle.
insertEdge :: (Alternative m, MonadState Proof m) => Edge -> Node -> Node -> m ()
insertEdge edge source target
  | source == target, not (isWellFounded edge) = empty
  | otherwise = do
    proof <- get
    let (change, edges) = alterAdjMap alterEdge source target (proofEdges proof)
    put (proof {proofEdges = edges})
    when change $
      close edges
  where
    alterEdge Nothing = (True, edge)
    alterEdge (Just edge')
      | edge `isAsStrongAsEdge` edge' = (False, edge' {edgeLabel = edgeLabel edge `firstJust` edgeLabel edge'})
      | edge' `isAsStrongAsEdge` edge = (True, edge {edgeLabel = edgeLabel edge `firstJust` edgeLabel edge'})
      | otherwise = (True, unionEdges edge edge')

    close edges = do
      let succs = fromMaybe IntMap.empty (IntMap.lookup target edges)
          preds = IntMap.mapMaybe (IntMap.lookup source) edges
      _ <- IntMap.traverseWithKey (\node edge' -> insertEdge (edge Prelude.<> edge') source node) succs
      _ <- IntMap.traverseWithKey (\node edge' -> insertEdge (edge' Prelude.<> edge) node target) preds
      pure ()

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
