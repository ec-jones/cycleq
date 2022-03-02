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
import CycleQ.Proof ()
import CycleQ.Prover
import Data.Bifunctor
import Data.Data
import qualified Data.Map as Map
import Data.Maybe
import GHC.Plugins hiding (empty)
import qualified Language.Haskell.TH as TH
import System.CPUTime

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
    { fuel = 11,
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
        pure (CoreDoPluginPass "CycleQ" cycleq : todo),
      pluginRecompile = purePlugin
    }

-- | Run cycleq proof earch on annotated top-level definitions.
cycleq :: ModGuts -> CoreM ModGuts
cycleq mguts = do
  results <-
    foldM
      ( \results -> \case
          (Annotation (NamedTarget goalName) ann)
            | Just params <- (fromSerialized deserializeWithData ann :: Maybe (CycleQ TH.Name)),
              Just goal <- ghcNameToEquation prog goalName -> do
              params' <- traverse (thNameToEquation prog) params
              putMsg (text "Property:" <+> ppr goalName)

              -- -- Output proof
              -- prover env (fuel params) (lemmas params') [goal] >>= \case
              --   (Nothing, _) -> pprPanic "Failed to prove:" (ppr goal)
              --   (Just proverState, Sum edgeInteger) ->
              --     unless (output params == "\0") $
              --       drawProof (proofGraph proverState) (output params')

              -- Benchmarking
              times <- replicateM 1 (benchmark params' goal)
              pure (Map.insert (occNameString $ occName goalName) times results)
          _ -> pure results
      )
      Map.empty
      (mg_anns mguts)
  liftIO $
    writeFile "benchmarks" (show $ bimap average average . unzip <$> results)
  pure mguts
  where
    prog :: CoreProgram
    prog = cleanProg $ mg_binds mguts

    env :: ProgramEnv
    env = mkProgramEnv prog

    average :: [Float] -> Float
    average xs = sum xs / fromIntegral (length xs)

    -- Run a particular benchmark once.
    benchmark :: CycleQ Equation -> Equation -> CoreM (Float, Float)
    benchmark params goal = do
      t0 <- liftIO getCPUTime
      prover env (fuel params) (lemmas params) [goal] >>= \case
        (Nothing, _) -> pprPanic "Failed to prove:" (ppr goal)
        (Just proverState, Sum edgeInteger) -> do
          t1 <- liftIO getCPUTime
          let totalTime, edgeTime :: Float
              totalTime = fromIntegral (t1 - t0) / 1000000000
              edgeTime = fromIntegral edgeInteger / 1000000000
          pure (totalTime, edgeTime)

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