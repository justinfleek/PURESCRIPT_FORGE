{-# LANGUAGE OverloadedStrings #-}
-- Main entry point for PureScript → C++23 → React compiler
module Main where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Environment
import System.Exit
import System.IO
import Parser
import TypeChecker
import Cpp23Generator

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["compile", inputFile, outputDir] -> do
      content <- TIO.readFile inputFile
      case parseModule content of
        Left err -> do
          hPutStrLn stderr $ "Parse error: " ++ show err
          exitFailure
        Right module' -> do
          -- Type check
          case typeCheckModule module' of
            Left typeErr -> do
              hPutStrLn stderr $ "Type error: " ++ T.unpack typeErr
              exitFailure
            Right checkedModule -> do
              -- Generate C++23 header
              let header = generateCpp23Header checkedModule
              let headerName = outputDir ++ "/" ++ T.unpack (toCppHeaderName (moduleName checkedModule)) ++ ".hpp"
              TIO.writeFile headerName header
              
              -- Generate C++23 implementation
              let impl = generateCpp23Impl checkedModule
              let implName = outputDir ++ "/" ++ T.unpack (toCppHeaderName (moduleName checkedModule)) ++ ".cpp"
              TIO.writeFile implName impl
              
              putStrLn $ "Generated C++23 code:"
              putStrLn $ "  Header: " ++ headerName
              putStrLn $ "  Implementation: " ++ implName
              
              -- Then generate React code (would call cpp23-to-react tool)
              putStrLn "Compilation complete"
    _ -> do
      putStrLn "Usage: purescript-to-cpp23 compile <input.purs> <output-dir>"
      exitFailure

toCppHeaderName :: T.Text -> T.Text
toCppHeaderName = T.replace "." "_"
