#!/usr/bin/env runghc
{-# LANGUAGE OverloadedStrings #-}

-- |
-- test-unit: Run compiler pipeline unit tests
--
-- Runs all unit tests for the PureScript → C++23 compiler:
--   - parser-tests
--   - generator-tests
--   - typechecker-tests

import Shelly (shelly, run_, echo, liftIO, cd)
import qualified Data.Text as T
import System.Directory (doesDirectoryExist)
import System.Exit (exitWith)

main :: IO ()
main = shelly $ do
    echo "=== Running Compiler Pipeline Tests ==="
    
    -- Change to test directory
    let testDir = "src/compiler-pipeline/purescript-to-cpp23"
    dirExists <- liftIO $ doesDirectoryExist testDir
    
    if dirExists
        then do
            cd testDir
            echo $ "Changed to: " <> T.pack testDir
            
            -- Run parser tests
            echo "Running parser-tests..."
            run_ "cabal" ["test", "parser-tests"]
            
            -- Run generator tests
            echo "Running generator-tests..."
            run_ "cabal" ["test", "generator-tests"]
            
            -- Run typechecker tests
            echo "Running typechecker-tests..."
            run_ "cabal" ["test", "typechecker-tests"]
            
            echo "=== All tests passed ==="
        else do
            echo $ "Error: Directory not found: " <> T.pack testDir
            liftIO $ exitWith 1
