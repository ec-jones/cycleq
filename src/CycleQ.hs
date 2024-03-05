module CycleQ
  ( plugin,

    -- * Paramters
    Params (..),
    defaultParams,
    assumption,

    -- * Formulas
    Formula,
    (===),
    (/\),
    (==>),
  )
where

import Control.Monad
import Control.Monad.Trans
import CycleQ.Prover
import CycleQ.Proof.Proof qualified as Proof
import CycleQ.Syntax
import CycleQ.Syntax.Translation
import Data.Data
import Data.Map qualified as Map
import Data.List qualified as List
import Data.Time.Clock
import GHC.Plugins qualified as GHC
import Language.Haskell.TH qualified as TH

-- | The Cycleq plugin.
plugin :: GHC.Plugin
plugin =
  GHC.defaultPlugin
    { GHC.installCoreToDos = \opts _ ->
        pure [GHC.CoreDoPluginPass "CycleQ" cycleq]
    }

-- | Run the cycleq prover on each annotated problem in a module.
cycleq :: GHC.ModGuts -> GHC.CoreM GHC.ModGuts
cycleq mguts = do
  GHC.putMsgS "Translating program..."

  -- Extract datatype environment and program.
  (dataTypeEnv, program, clauses) <- translateModule mguts

  let ?program = program
      ?dataTypeEnv = dataTypeEnv

  let ?online = True
      ?conditional = True

  GHC.putMsgS ""

  stats <- 
    forM (Map.toList clauses) $ \case
      -- Assumption
        (clauesName, (Assumption, _)) -> pure Nothing

        -- Assertion
        (clauseName, (params@Assertion{}, clause)) -> GHC.liftIO $ do
          putStrLn ("Attempting to prove: " ++ clauseName)
          t0 <- getCurrentTime

          let lemmaClauses = fmap (snd . (clauses Map.!)) (lemmas params)
          case prover (fuel params) lemmaClauses [clause] of
            (Nothing, acc) -> do
              putStrLn "Fail!"
              -- print acc
              pure Nothing
            (Just st, acc)-> do
              t1 <- GHC.liftIO getCurrentTime
              print (diffUTCTime t1 t0)

              putStrLn "Success!"
              -- putStrLn ("Unoriented: " ++ show acc)
              unless (output params == "\0") $
                Proof.drawProof (proverProof st) (output params)
              
              let sz = Proof.size (proverProof st)
              pure (Just (sz, diffUTCTime t1 t0))

  let stats' :: [Float]
      stats' = [ realToFrac delta * 1000 | Just (sz, delta) <- stats]
      
  let cumulative :: [(Float, Int)]
      cumulative = zip (List.sort stats') [1 ..] 
      
  GHC.putMsgS (show cumulative)

  pure mguts

-- | Clauses appearing in the module.
type Clauses =
  Map.Map String (Params String, Clause)

-- | Translate to-level binds in a module.
translateModule :: GHC.ModGuts -> GHC.CoreM (DataTypeEnv, Program, Clauses)
translateModule mguts =
  translate $ foldM go Map.empty (GHC.flattenBinds (GHC.mg_binds mguts))
  where
    -- Module annotation environment
    annEnv :: GHC.AnnEnv
    annEnv = GHC.mkAnnEnv (GHC.mg_anns mguts)

    -- Find the annotations associated with a bind
    findAnns :: GHC.CoreBndr -> [Params TH.Name]
    findAnns x =
      GHC.findAnns GHC.deserializeWithData annEnv (GHC.NamedTarget (GHC.getName x))

    go :: Clauses -> (GHC.CoreBndr, GHC.CoreExpr) -> TranslateT GHC.CoreM Clauses
    go clauses (x, defn) = do
      -- Variables bound at the top-level
      let ?freeVars = []
          ?inScopeSet =
            GHC.mkInScopeSet $ GHC.mkVarSet $ GHC.bindersOfBinds (GHC.mg_binds mguts)

      -- Check if bind genuinely exists in the source
      let srcSpan = GHC.getSrcSpan x
      if GHC.isGoodSrcSpan srcSpan && not (GHC.isZeroWidthSpan srcSpan)
        then do
          case findAnns x of
            [] ->
              -- Translate function
              catchError
                ( do
                    translateBind x defn
                    pure clauses
                )
                $ \err -> lift $ do
                  GHC.putMsg
                    ( GHC.text "[Warning] Couldn't translate function '"
                        GHC.<> GHC.ppr x
                        GHC.<> GHC.text "':"
                        GHC.<+> GHC.ppr err
                    )
                  pure clauses
            (params : _) ->
              -- Translate clause
              catchError
                ( do
                    clause <- translateClause defn

                    -- Find lemmas
                    params' <- forM params $ \lemmaName ->
                      lift (GHC.thNameToGhcName lemmaName) >>= \case
                        Nothing ->
                          pure (Left lemmaName)
                        Just lemmaName' ->
                          pure (Right (GHC.occNameString (GHC.occName lemmaName')))

                    case sequence params' of
                      Left lemmaName -> do
                        lift $
                          GHC.putMsg
                            ( GHC.text "[Warning] Couldn't find lemma '"
                                GHC.<> GHC.text (show lemmaName)
                                GHC.<> GHC.text "'"
                            )
                        pure clauses
                      Right params' ->
                        let name = GHC.occNameString (GHC.occName x)
                         in pure (Map.insert name (params', clause) clauses)
                )
                $ \err -> lift $ do
                  GHC.putMsg
                    ( GHC.text "[Warning] Couldn't translate clause '"
                        GHC.<> GHC.ppr x
                        GHC.<> GHC.text "':"
                        GHC.<+> GHC.ppr err
                    )
                  pure clauses
        else pure clauses

-- * Formulas

-- | CycleQ parameters.
data Params a
  = Assumption
  | Assertion
      { fuel :: Int,
        output :: FilePath,
        lemmas :: [a]
      }
      deriving stock (Functor, Foldable, Traversable, Data)

-- | An assertion that is to be proven 10 fuel and no lemmas or output file.
defaultParams :: Params TH.Name
defaultParams =
  Assertion
    { fuel = 10,
      output = "\0",
      lemmas = []
    }

-- | A clause that is assumed true without proof.
assumption :: Params TH.Name
assumption = Assumption

-- | CycleQ formulas
data Formula

infix 0 ==>

infix 2 ===

infixr 1 /\

-- | Atomic equation.
(===) :: a -> a -> Formula
(===) = undefined

-- | Conjunction.
(/\) :: Formula -> Formula -> Formula
(/\) = undefined

-- | Implication.
(==>) :: Formula -> Formula -> Formula
(==>) = undefined
