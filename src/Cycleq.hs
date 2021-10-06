module Cycleq
  ( plugin,
    Equation,
    (≃),
  )
where

import Cycleq.Prover
import Cycleq.Equation
import Data.Maybe
import Cycleq.Proof
import Control.Monad.Reader
import Data.Bifunctor
import Cycleq.Environment
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
            let prog = map cleanBind (mg_binds mguts)
            case [ defn
                   | (x, defn) <- flattenBinds prog,
                     getOccName (getName x) == mkVarOcc "prop"
                 ] of
              [] -> pure ()
              (main : _) -> do
                let equation = fromJust $ equationFromCore main
                mproof <- runReaderT (prover equation) (mkProgramEnv prog)
                case mproof of
                  Nothing -> 
                    putMsgS "Failure!"
                  Just proof -> 
                drawProof proof "proof.svg"
            pure mguts
        )

-- | Clean up core expressions by removing ticks and checking they can be handled.
cleanCore :: CoreExpr -> CoreExpr
cleanCore (Var x) = Var x
cleanCore (Lit lit) = Lit lit
cleanCore expr@(App _ _) =
  case collectArgs expr of
    (Let _ _, args)
      | not (null args) -> 
        pprSorry "Higher-order let expressions are not yet supported!" (ppr expr)  
    (fun, args) -> mkApps (cleanCore fun) (map cleanCore args)
cleanCore (Lam x body) = Lam x (cleanCore body)
cleanCore (Let bind body) = Let (cleanBind bind) (cleanCore body)
cleanCore (Case scrut x ty cases) = Case (cleanCore scrut) x ty (map cleanAlt cases)
cleanCore (Tick _ expr) = cleanCore expr
cleanCore (Type ty) = Type ty
cleanCore expr = pprSorry "Casts and coercions are not yet supported!" (ppr expr)

-- | Clean up core binds.
cleanBind :: CoreBind -> CoreBind
cleanBind (NonRec x defn) = NonRec x (cleanCore defn)
cleanBind (Rec defns) = Rec (map (second cleanCore) defns)

-- | Clean up case alternative.
cleanAlt :: CoreAlt -> CoreAlt
cleanAlt (ac, xs, rhs) = (ac, xs, cleanCore rhs)