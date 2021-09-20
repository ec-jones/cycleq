module Cycleq
  ( plugin,
    Equation,
    (≃),
  )
where

import Control.Monad.Freer
import Control.Monad.Freer.NonDet
import Control.Monad.Freer.Reader
import Control.Monad.Freer.State
import Cycleq.Prover
import Cycleq.Equation
import Cycleq.Proof
import Cycleq.Reduction
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
            case [ defn
                   | (x, defn) <- flattenBinds (mg_binds mguts),
                     getOccName (getName x) == mkVarOcc "main"
                 ] of
              [] -> pure ()
              (main : _) -> do
                let equation = fromCore main
                proof <-
                  runM $
                    makeChoiceA
                      ( execState
                          emptyProof
                          (runReader (mkContext (cleanBind <$> mg_binds mguts)) (prover equation))
                      )
                drawProof (head proof) "proof.svg"
            pure mguts
        )