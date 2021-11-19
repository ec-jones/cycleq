module Main where

import Cycleq
import GHC as G
import GHC.Driver.Session
import GHC.Types.SrcLoc as G
import GHC.Plugins

import Control.Monad
import Control.Monad.IO.Class
import System.Environment

-- cabal run profile -- +RTS -pj -l-au
-- https://www.speedscope.app/

initGhcM :: [String] -> Ghc ()
initGhcM xs = do
  df1 <- getSessionDynFlags
  let df1' = df1{staticPlugins = [StaticPlugin (PluginWithArgs plugin [])]}
  let cmdOpts = "-fforce-recomp" : xs
  (df2, leftovers, warns) <- G.parseDynamicFlags df1' (map G.noLoc cmdOpts)
  setSessionDynFlags df2
  ts <- mapM (flip G.guessTarget Nothing . unLoc) leftovers

  setTargets ts

  void $ G.load LoadAllTargets

main :: IO ()
main = do
  let libdir = "/home/eddie/.ghcup/ghc/9.0.1/lib/ghc-9.0.1"
  xs <- words <$> readFile "./profile/ghc-options"
  runGhc (Just libdir) $ initGhcM xs