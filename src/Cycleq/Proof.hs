{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DerivingStrategies #-}

module Cycleq.Proof where

import Control.Applicative
import Control.Monad
import Control.Monad.Freer
import Control.Monad.Freer.NonDet
import Control.Monad.Freer.State
import Cycleq.Edge
import Cycleq.Equation
import Data.GraphViz
import Data.GraphViz.Attributes.Complete
import qualified Data.IntMap as IntMap
import Data.Maybe
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.IO as Text
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
    proofRules :: IntMap.IntMap (Maybe Rule)
  }

-- | The inference rules.
data Rule
  = Refl
  | Reduce
  | Cong
  | Case
  | FunExt
  | Super
  deriving stock Eq

-- | An initial proof with no nodes or edges.
emptyProof :: Proof
emptyProof =
  Proof
    { proofNodes = IntMap.empty,
      proofEdges = IntMap.empty,
      proofRules = IntMap.empty
    }

-- | Insert a equation into a proof and return the new node's index.
insertNode :: Member (State Proof) es => Equation -> Eff es Node
insertNode equation = do
  proof@Proof { proofNodes, proofRules } <- get
  case IntMap.lookupMax proofNodes of
    Nothing -> do
      put
        ( proof
            { proofNodes = IntMap.singleton 0 equation,
              proofRules = IntMap.insert 0 Nothing proofRules
            }
        )
      pure 0
    Just (n, _) -> do
      put
        ( proof
            { proofNodes = IntMap.insert (n + 1) equation proofNodes,
              proofRules = IntMap.insert (n + 1) Nothing proofRules
            }
        )
      pure (n + 1)

-- | Mark a node as completed.
markNodeAsComplete :: Member (State Proof) es => Node -> Rule -> Eff es ()
markNodeAsComplete node rule = modify (\proof -> proof {proofRules = IntMap.insert node (Just rule) (proofRules proof)})

-- | The set of complete proof nodes
caseProofNodes :: Proof -> [Node]
caseProofNodes Proof {proofRules} =
  IntMap.keys $ IntMap.filter (== Just Cycleq.Proof.Case) proofRules

incompleteNodes :: Proof -> [Node]
incompleteNodes Proof {proofRules} =
  IntMap.keys $ IntMap.filter (== Nothing) proofRules

-- | Get the equation of a given node.
lookupNode :: Member (State Proof) es => Node -> Eff es Equation
lookupNode node = do
  Proof {proofNodes} <- get
  case IntMap.lookup node proofNodes of
    Nothing -> pprPanic "Node not in graph!" (ppr node)
    Just equation -> pure equation

-- | Insert an edge into a proof and fail if this creates a cycle.
insertEdge :: (Member NonDet es, Member (State Proof) es) => Edge -> Node -> Node -> Eff es ()
insertEdge edge source target
  | source == target, not (isWellFounded edge) = empty
  | otherwise = do
    proof@Proof {proofEdges} <- get
    let (change, edges) = alterAdjMap alterEdge source target proofEdges
    put (proof {proofEdges = edges})
    when change $
      close proofEdges
  where
    alterEdge Nothing = (True, edge)
    alterEdge (Just edge')
      | edge `isAsStrongAsEdge` edge' = (False, edge' {edgeLabel = edgeLabel edge <|> edgeLabel edge'})
      | edge' `isAsStrongAsEdge` edge = (True, edge {edgeLabel = edgeLabel edge <|> edgeLabel edge'})
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
