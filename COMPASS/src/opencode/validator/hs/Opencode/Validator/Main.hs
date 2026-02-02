-- | Main entry point for OpenCode validators
-- | Phase 2: Type Safety Layer
module Opencode.Validator.Main where

import Opencode.Validator.BannedConstructs
import Opencode.Validator.FileReading
import Opencode.Validator.TypeEscapes
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
      putStrLn "  opencode-validator banned <path>"
      putStrLn "  opencode-validator file-reading <path>"
      putStrLn "  opencode-validator type-escapes <path>"
      exitFailure
