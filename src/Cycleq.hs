{-# LANGUAGE LambdaCase #-}

module Cycleq
  ( plugin,
    Equation,
    (≃),
  )
where

import Control.Monad.Reader
import Cycleq.Environment
import Cycleq.Equation
import Cycleq.Proof
import Cycleq.Prover
import Data.Bifunctor
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
            case [ (x', defn)
                   | (x, defn) <- flattenBinds prog,
                     Just x' <- pure ("goal_" `List.stripPrefix` occNameString (occName x))
                 ] of
              [] -> putMsgS "Couldn't find a goal!"
              goals -> forM_ goals $ \(x, goal) -> do
                putMsgS ("Attempting to prove: " ++ x)
                let equation = fromJust $ equationFromCore goal
                runReaderT (prover equation) (mkProgramEnv prog) >>= \case
                  Nothing -> putMsgS "Failure!"
                  Just proof -> do
                    putMsgS "Success!"
                    drawProof proof ("proof_" ++ x ++ ".svg")
            pure mguts
        )

-- | Clean up a core program by removing ticks and join points.
-- N.B. This function fails on unsuported expressions like casts and coercions.
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
    go (Let bind body) = Let (goBind bind) (go body)
    go (Case scrut x ty cases) = Case (go scrut) x ty (map goAlt cases)
    go (Tick _ expr) = go expr
    go (Type ty) = Type ty
    go expr = pprSorry "Casts and coercions are not yet supported!" (ppr expr)

    goBind :: CoreBind -> CoreBind
    goBind (NonRec x defn) = NonRec x (go defn)
    goBind (Rec defns) = Rec (map (second go) defns)

    goAlt :: CoreAlt -> CoreAlt
    goAlt (ac, xs, rhs) = (ac, xs, go rhs)
