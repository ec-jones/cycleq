{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UnicodeSyntax #-}

module Cycleq
  ( plugin,

    -- * Equations and Sequents
    Equation,
    (≃),
    Sequent,
    Syntax.IsSequent,
    (⊢),

    -- * Commands
    Command,
    Syntax.normaliseTerm,
    Syntax.criticalTerms,
    Syntax.simplifyEquation,
    Syntax.simplifySequent
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
handleCommand mguts (NormaliseTerm (Sequent fvs ante expr)) =
  let ctx = addFreeVars fvs $ progContext (mg_binds mguts)
      res = runReader (Normalisation.normaliseTerm ante expr) ctx
   in putMsg (ppr res)
handleCommand mguts (CriticalTerms (Sequent fvs ante expr)) =
  let ctx = addFreeVars fvs $ progContext (mg_binds mguts)
      res = runReader (Normalisation.criticalTerms ante expr) ctx
   in putMsg (ppr res)
handleCommand mguts (SimplifyEquation (Sequent fvs ante expr)) =
  let ctx = addFreeVars fvs $ progContext (mg_binds mguts)
      res = runReader (Normalisation.simplifyEquation ante expr) ctx
   in putMsg (ppr res)
handleCommand mguts (SimplifySequent sequent) =
  let ctx = progContext (mg_binds mguts)
      res = runReader (Normalisation.simplifySequent sequent) ctx
   in putMsg (ppr res)