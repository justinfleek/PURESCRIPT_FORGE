{-# LANGUAGE StrictData #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Spec loader CLI
module Main where

import Prelude hiding (head, tail, undefined, error)
import SpecLoader
import SpecLoader.Types
import Data.Text.IO (putStrLn)
import qualified Data.Text as T
import Data.Text (pack)
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)

main :: IO ()
main = do
  args <- getArgs
  let specPath = case args of
        [path] -> path
        _ -> "forge-sidepanel-specs"
  
  result <- loadAllSpecs specPath
  
  case result of
    LoadFailure err -> do
      putStrLn $ "Failed to load specs: " <> err
      exitFailure
    
    LoadSuccess suite -> do
      putStrLn $ "Loaded " <> pack (show (suiteTotal suite)) <> " specification files"
      
      if verifySpecCount suite
        then do
          putStrLn "✅ All 99 specs present"
          exitSuccess
        else do
          putStrLn $ "⚠️  Expected 99 specs, found " <> pack (show (suiteTotal suite))
          exitFailure
