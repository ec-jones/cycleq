{-# LANGUAGE LambdaCase #-}

module Cycleq
  ( plugin,
    Equation,
    (≃),
  )
where

import Numeric (showFFloat)
import Control.Monad.Reader
import Cycleq.Environment
import Cycleq.Equation
import Cycleq.Proof
import Cycleq.Prover
import System.CPUTime
import Data.Bifunctor
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Maybe
import GHC.Plugins hiding (empty)

-- | Construct an equation between two terms.
(≃) :: a -> a -> Equation
(≃) = (≃)

infix 4 ≃

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
                go0 results (x, goal) =
                  case "goal_" `List.stripPrefix` occNameString (occName x) of
                      Nothing -> pure results
                      Just goalName -> do
                        putMsgS ("Attempting to prove: " ++ goalName)
                        t0 <- liftIO getCPUTime
                        let equation = fromJust $ equationFromCore goal
                        runReaderT (prover equation) (mkProgramEnv prog) >>= \case
                          Nothing -> pure (Map.insert (read goalName :: Int) Nothing results)
                          Just proof -> do
                            putMsgS ("Success!")
                            t1 <- liftIO getCPUTime
                            ts <- replicateM 9 (goN equation)
                            pure (Map.insert (read goalName) (Just (t1 - t0 : ts)) results)
                goN equation = do
                  t0 <- liftIO getCPUTime
                  runReaderT (prover equation) (mkProgramEnv prog) >>= \case
                    Just proof -> do
                      t1 <- liftIO getCPUTime
                      pure (t1 - t0)
            res <- foldM go0 Map.empty (flattenBinds prog)
            putMsgS (show $ Map.size $ Map.filter isJust res)
            putMsgS (show $ Map.size res)
            putMsgS (show $ sum $ sum <$> Map.mapMaybe id res)
            liftIO $ writeFile "benchmark" (showMark res)
            pure mguts
        )

-- | Convert benchmark to latex tabular
showMark :: Map.Map Int (Maybe [Integer]) -> String
showMark bm =
    unlines $ pre ++ titles : Map.foldrWithKey (\k v ss -> entry k v : ss) post bm
  where
    pre = ["\\begin{tabular}{|l|l|}", "\\hline"]
    titles = concat $ List.intersperse " & " ["Name", "Time (ms)"] ++ ["\\\\\\hline"]
    entry n Nothing = concat $ List.intersperse " & " [show n, "X"] ++ ["\\\\\\hline"]
    entry n (Just xs) = concat $ List.intersperse " & " [show n, showFFloat (Just 2) (avg xs / fromIntegral 1000000000) ""] ++ ["\\\\\\hline"]
    avg xs = fromIntegral (sum xs) / fromIntegral (length xs)
    post = ["\\end{tabular}"]

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
