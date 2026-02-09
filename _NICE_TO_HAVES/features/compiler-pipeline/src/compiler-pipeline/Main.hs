-- Main entry point for PureScript → C++23 → React compiler
module Main where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Environment
import System.Exit
import Parser
import Cpp23Generator

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["compile", inputFile, outputDir] -> do
      content <- TIO.readFile inputFile
      case parseModule content of
        Left err -> do
          putStrLn $ "Parse error: " ++ show err
          exitFailure
        Right module' -> do
          let cpp23 = generateCpp23 module'
          TIO.writeFile (outputDir ++ "/generated.cpp") cpp23
          putStrLn "Generated C++23 code"
          
          -- Then generate React code
          -- (This would call cpp23-to-react tool)
          putStrLn "Compilation complete"
    _ -> do
      putStrLn "Usage: compiler-pipeline compile <input.purs> <output-dir>"
      exitFailure
