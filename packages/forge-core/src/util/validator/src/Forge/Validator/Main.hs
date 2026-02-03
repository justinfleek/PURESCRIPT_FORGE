-- | Main entry point for Forge validators
-- | Phase 2: Type Safety Layer
module Forge.Validator.Main where

import Forge.Validator.BannedConstructs
import Forge.Validator.FileReading
import Forge.Validator.TypeEscapes
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["banned", path] -> do
      result <- BannedConstructs.validateDirectory path
      case result of
        Left err -> do
          putStrLn "Banned constructs found:"
          putStrLn err
          exitFailure
        Right [] -> do
          putStrLn "No banned constructs found."
          exitSuccess
        Right violations -> do
          putStrLn "Banned constructs found:"
          mapM_ putStrLn violations
          exitFailure
    ["file-reading", path] -> do
      result <- FileReading.validateDirectory path
      case result of
        Left err -> do
          putStrLn "File reading violations found:"
          putStrLn err
          exitFailure
        Right [] -> do
          putStrLn "File reading protocol compliant."
          exitSuccess
        Right violations -> do
          putStrLn "File reading violations found:"
          mapM_ putStrLn violations
          exitFailure
    ["type-escapes", path] -> do
      TypeEscapes.validateDirectory path
      putStrLn "Type escape check complete."
      exitSuccess
    _ -> do
      putStrLn "Usage:"
      putStrLn "  forge-validator banned <path>"
      putStrLn "  forge-validator file-reading <path>"
      putStrLn "  forge-validator type-escapes <path>"
      exitFailure
