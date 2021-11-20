{-# LANGUAGE LambdaCase #-}

module Cycleq
  ( plugin,
    Equation,
    (===),
  )
where

import Control.Monad.Reader
import Cycleq.Environment
import Cycleq.Equation
import Cycleq.Proof
import Cycleq.Prover
import Data.Bifunctor
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe
import GHC.Plugins hiding (empty)
import Numeric (showFFloat)
import System.CPUTime

-- | Construct an equation between two terms.
(===) :: a -> a -> Equation
(===) = (===)

infix 0 ===

-- | The Cycleq plugin.
plugin :: Plugin
plugin =
  defaultPlugin
    { installCoreToDos = \_ _ -> pure [pass],
      pluginRecompile = purePlugin
    }
  where
    pass =
      CoreDoPluginPass
        "Cycleq"
        ( \mguts -> do
            let prog = cleanProg (mg_binds mguts)
                -- Attempt to prove goal with n iterations
                prove n results (x, goal) =
                  case "prop_" `List.stripPrefix` occNameString (occName x) of
                    Nothing -> pure results
                    Just goalName -> do
                      putMsgS ("Attempting to prove: " ++ goalName)
                      let equation = fromJust $ equationFromCore goal
                      t0 <- liftIO getCPUTime
                      runReaderT (prover False equation) (mkProgramEnv prog) >>= \case
                        Nothing -> pure (Map.insert (read goalName :: Int) Nothing results)
                        Just (fuel, proof) -> do
                          t1 <- liftIO getCPUTime
                          -- putMsgS "Success!"
                          -- putMsgS ("Fuel: " ++ show fuel)
                          ts <- replicateM (n - 1) (go equation)
                          -- putMsgS
                          --   ( "Total time: "
                          --       ++ showFFloat
                          --         (Just 2)
                          --         (fromIntegral (t1 - t0) / fromIntegral 1000000000)
                          --         ""
                          --   )
                          -- putMsgS
                          --   ( "Edge time: "
                          --       ++ showFFloat
                          --         (Just 2)
                          --         (fromIntegral (proofEdgeTime proof) / fromIntegral 1000000000)
                          --         ""
                          --   )
                          pure (Map.insert (read goalName) (Just ((t1 - t0, proofEdgeTime proof) : ts)) results)
                -- Iterate
                go equation = do
                  t0 <- liftIO getCPUTime
                  runReaderT (prover False equation) (mkProgramEnv prog) >>= \case
                    Nothing -> pprPanic "Unexpected proof failure!" (ppr equation)
                    Just (_, proof) -> do
                      t1 <- liftIO getCPUTime
                      pure (t1 - t0, proofEdgeTime proof)

            res <- foldM (prove 10) Map.empty (flattenBinds prog)

            -- putMsgS ("No. Problems: " ++ show (Map.size res))
            -- putMsgS ("Total solved: " ++ show (Map.size $ Map.filter isJust res))
            liftIO $ writeFile "benchmark.tex" (showMark res)
            pure mguts
        )

-- | Convert benchmark to latex tabular
showMark :: Map.Map Int (Maybe [(Integer, Integer)]) -> String
showMark bm =
  unlines $ pre ++ titles : Map.foldrWithKey (\k v ss -> entry k v : ss) post bm
  where
    pre = ["\\begin{tabular}{llll}", "\\toprule"]
    titles = concat $ List.intersperse " & " ["Name", "Total Time (ms)", "Edge Time (ms)", "Edge Time (\\%)"] ++ ["\\\\\\midrule"]
    post = ["\\bottomrule", "\\end{tabular}"]

    -- Format an entry
    entry n Nothing = concat $ List.intersperse " & " [show n, "X"] ++ ["\\\\\\midrule"]
    entry n (Just xs) =
      let (total, edge, percent) = stats xs
       in 
      concat $
        List.intersperse
          " & "
          [show n, showFFloat (Just 2) total "", showFFloat (Just 2) edge "", showFFloat (Just 2) percent ""]
          ++ ["\\\\\\midrule"]

    -- Compute the average time and edge percentage
    stats :: [(Integer, Integer)] -> (Float, Float, Float)
    stats xs =
      ( sum (map (fromIntegral . fst) xs) / (fromIntegral (length xs) * 1000000000),
        sum (map (fromIntegral . snd) xs) / (fromIntegral (length xs) * 1000000000),
        100 * sum (map (\(t, e) -> fromIntegral e / fromIntegral t) xs) / (fromIntegral (length xs))
      )

-- | Clean up a core program by removing ticks and join points.
cleanProg :: CoreProgram -> CoreProgram
cleanProg prog = map goBind prog
  where
    scope :: InScopeSet
    scope = mkInScopeSet $ mkVarSet $ bindersOfBinds prog

    go :: CoreExpr -> CoreExpr
    go (Var x) = Var x
    go (Lit lit) = Lit lit
    go (App fun arg) = App (go fun) (go arg)
    go (Lam x body) = Lam x (go body)
    go (Let bind@(NonRec x defn) body)
      | Just _ <- bndrIsJoin_maybe x =
        -- Inline join points
        let subst = mkOpenSubst scope [(x, defn)]
         in go (substExpr subst body)
    go (Let bind body) =
      pprSorry
        "Local let binds are not yet supported!\
        \ Try adding a type signature to the top-level definition"
        (ppr ())
    go (Case scrut x ty cases) = Case (go scrut) x ty (map goAlt cases)
    go (Tick _ expr) = go expr
    go (Type ty) = Type ty
    go expr = pprSorry "Casts and Coercions are not yet supported!" (ppr ())

    goBind :: CoreBind -> CoreBind
    goBind (NonRec x defn) = NonRec x (go defn)
    goBind (Rec defns) = Rec (map (second go) defns)

    goAlt :: CoreAlt -> CoreAlt
    goAlt (ac, xs, rhs) = (ac, xs, go rhs)
