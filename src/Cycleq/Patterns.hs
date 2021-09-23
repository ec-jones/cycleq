{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
-- |
-- Module      : Cycleq.Patterns
-- This module defines common patterns of core expressions used throughout the project.
module Cycleq.Patterns 
  ( pattern Apps,
    pattern Lams,
    pattern ConApp,
    pattern Lit'
  )
  where

import GHC.Plugins

-- | A non-application expression applied to a list of arguments.
pattern Apps :: CoreExpr -> [CoreArg] -> CoreExpr
pattern Apps fun args <- (collectArgs -> (fun, args))
  where
    Apps fun args = mkApps fun args

-- | Decompose an expression into term-level lambdas and the body. 
pattern Lams :: [Id] -> CoreExpr -> CoreExpr
pattern Lams xs body <- (collectBinders -> (filter isId -> xs, body))

-- | Core expressions that are the application of a data constructor to several arguments.
pattern ConApp :: DataCon -> [CoreArg] -> CoreExpr
pattern ConApp con args <-
  (viewConApp -> Just (con, args))
  where
    ConApp con args = mkCoreConApps con args

viewConApp :: CoreExpr -> Maybe (DataCon, [CoreArg])
viewConApp = go [] []
  where
    go binds args (Var x) = do
      con <- isDataConWorkId_maybe x
      pure (con, fmap (\arg -> foldr Let arg binds) args)
    go binds args (App fun arg) = go binds (arg : args) fun
    go binds [] (Let bind body) = go (bind : binds) [] body
    go _ _ _ = Nothing

-- | Core expressions that are literals under a number of let-bindings.
pattern Lit' :: Literal -> CoreExpr
pattern Lit' lit <-
  (viewLit -> Just lit)
  where
    Lit' lit = Lit lit

viewLit :: CoreExpr -> Maybe Literal
viewLit (Lit lit) = Just lit
viewLit (Let _ body) = viewLit body
viewLit _ = Nothing