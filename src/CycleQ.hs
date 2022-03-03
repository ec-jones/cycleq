{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}

module CycleQ
  ( CycleQ (..),
    defaultParams,
    Equation,
    (===),
    plugin,
  )
where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer
import CycleQ.Environment
import CycleQ.Equation
import CycleQ.Proof
import CycleQ.Prover
import Data.Bifunctor
import Data.Data
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe
import GHC.Plugins hiding (empty)
import qualified Language.Haskell.TH as TH
import Numeric (showFFloat)
import System.CPUTime
import System.IO

-- | CycleQ parameters.
data CycleQ a = CycleQ
  { fuel :: Int,
    output :: FilePath,
    lemmas :: [a]
  }
  deriving stock (Functor, Foldable, Traversable, Data)

-- | Default parameters
defaultParams :: CycleQ TH.Name
defaultParams =
  CycleQ
    { fuel = 12,
      output = "\0",
      lemmas = []
    }

-- | Construct an equation between two terms.
(===) :: a -> a -> Equation
(===) = (===)

infix 0 ===

-- | The Cycleq plugin.
plugin :: Plugin
plugin =
  defaultPlugin
    { installCoreToDos = \opts todo ->
        pure (CoreDoPluginPass "CycleQ" (cycleq ("benchmark" `elem` opts)) : todo),
      pluginRecompile = purePlugin
    }

-- | Run the cycleq prover on each annotated problem in a module.
cycleq :: Bool -> ModGuts -> CoreM ModGuts
cycleq benchmark mguts = do
  let modName = moduleNameString (moduleName (mg_module mguts))

  iters <-
    if benchmark
      then liftIO $ do
        putStr ("Benchmarking " ++ modName ++ "\nNo. of runs: ")
        hFlush stdout
        readLn
      else pure 0

  results <-
    foldM
      ( \results -> \case
          (Annotation (NamedTarget goalName) ann)
            | Just params <- (fromSerialized deserializeWithData ann :: Maybe (CycleQ TH.Name)),
              Just goal <- ghcNameToEquation prog goalName -> do
              params' <- traverse (thNameToEquation prog) params

              if benchmark
                then do
                  -- Benchmarking
                  putMsg (text "Benchmarking:" <+> ppr goalName)
                  times <- catMaybes <$> replicateM iters (runBenchmark params' goal)
                  pure (Map.insert (occNameString $ occName goalName) times results)
                else do
                  -- Output proof
                  putMsg (text "Attempting to prove:" <+> ppr goalName)
                  prover env (fuel params) (lemmas params') [goal] >>= \case
                    (Nothing, _) -> putMsgS "Fail!"
                    (Just proverState, Sum edgeInteger) -> do
                      putMsgS "Success!"
                      unless (output params == "\0") $
                        drawProof (proofGraph proverState) (output params')
                  pure results
          _ -> pure results
      )
      Map.empty
      (mg_anns mguts)

  -- Write out benchmarks
  when benchmark $ do
    liftIO $
      writeFile ("benchmarks - " ++ modName ++ ".tex") (showBenchmark results)

    let averageTime :: Double
        averageTime = average $ fmap (average . fmap fst) results
    putMsgS ("Average time: " ++ show averageTime)

  pure mguts
  where
    -- Clean-up program.
    prog :: CoreProgram
    prog = cleanProg $ mg_binds mguts

    -- Top-level program environment.
    env :: ProgramEnv
    env = mkProgramEnv prog

    -- Run a particular benchmark once.
    runBenchmark :: CycleQ Equation -> Equation -> CoreM (Maybe (Double, Double))
    runBenchmark params goal = do
      t0 <- liftIO getCPUTime
      prover env (fuel params) (lemmas params) [goal] >>= \case
        (Nothing, _) -> pure Nothing
        (Just proverState, Sum edgeInteger) -> do
          t1 <- liftIO getCPUTime
          let totalTime, edgeTime :: Double
              totalTime = fromIntegral (t1 - t0) / 1000000000
              edgeTime = fromIntegral edgeInteger / 1000000000
          pure (Just (totalTime, edgeTime))

-- | Find an equation from a TemplateHaskell name.
thNameToEquation :: CoreProgram -> TH.Name -> CoreM Equation
thNameToEquation prog =
  thNameToGhcName
    >=> ( \case
            Just name
              | Just equation <- ghcNameToEquation prog name ->
                pure equation
            _ -> pprPanic "Could not find eqation!" (ppr ())
        )

-- | Find an equation from a GHC name.
ghcNameToEquation :: CoreProgram -> Name -> Maybe Equation
ghcNameToEquation prog name =
  listToMaybe $
    mapMaybe
      ( \case
          NonRec x expr
            | getName x == name -> equationFromCore expr
          _ -> Nothing
      )
      prog

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

-- | Convert benchmark to latex tabular
showBenchmark :: Map.Map String [(Double, Double)] -> String
showBenchmark bm =
  unlines $ pre ++ titles : Map.foldrWithKey (\k v ss -> entry k v : ss) post bm
  where
    pre, post :: [String]
    pre = ["\\begin{tabular}{|llll|}", "\\hline"]
    post = ["\\hline", "\\end{tabular}"]

    titles :: String
    titles = concat $ List.intersperse " & " ["Name", "Total Time (ms)", "Edge Time (ms)", "Edge Time (\\%)"] ++ ["\\\\\\hline"]

    entry :: String -> [(Double, Double)] -> String
    entry n sts =
      let total = average (fmap fst sts)
          edge = average (fmap snd sts)
          percent = 100 * (edge / total)
       in concat $
            List.intersperse
              " & "
              [n, showFFloat (Just 3) total "", showFFloat (Just 3) edge "", showFFloat (Just 3) percent ""]
              ++ ["\\\\\\midrule"]

-- | Take an average over a foldable structure.
average :: Foldable f => f Double -> Double
average xs = sum xs / fromIntegral (length xs)
