{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UnicodeSyntax #-}

module Cycleq
  ( plugin,

    -- * Equations and Sequents
    Equation,
    Sequent,
    (≃),
    (⊢),

    -- * Commands
    Command,
    Syntax.normalise,
    Syntax.criticalTerms,
    Syntax.isProductive,
  )
where

import Control.Monad.Reader
import GHC.Plugins
import Normalisation
import Syntax

-- | The Cycleq plugin processes a list of commands at compile time.
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
                     getOccName (getName x) == mkVarOcc "commands"
                 ] of
              [] -> pure ()
              (commands : _) -> mapM_ (handleCommand mguts) (decodeCore commands :: [Command])
            pure mguts
        )

-- | Evalate a command
handleCommand :: ModGuts -> Command -> CoreM ()
handleCommand mguts (Normalise (Sequent fvs ante expr)) =
  let ctx = addFreeVars fvs $ progContext (mg_binds mguts)
      res = runReader (Normalisation.normalise ante expr) ctx
   in putMsg (ppr res)
handleCommand mguts (CriticalTerms (Sequent fvs ante expr)) =
  let ctx = addFreeVars fvs $ progContext (mg_binds mguts)
      res = runReader (Normalisation.criticalTerms ante expr) ctx
   in putMsg (ppr res)
handleCommand mguts (IsProductive (Sequent fvs ante expr)) =
  let ctx = addFreeVars fvs $ progContext (mg_binds mguts)
      res = runReader (Normalisation.isProductive ante expr) ctx
   in putMsg (ppr res)
