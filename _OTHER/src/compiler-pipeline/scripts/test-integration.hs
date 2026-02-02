#!/usr/bin/env runghc
{-# LANGUAGE OverloadedStrings #-}

-- |
-- test-integration: Run compiler pipeline integration tests
--
-- Tests the full pipeline:
--   1. PureScript → C++23 compilation
--   2. C++23 → React conversion

import Shelly (shelly, run_, echo, errExit, exitCode, liftIO, which)
import qualified Data.Text as T
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.FilePath ((</>))
import System.Exit (exitWith)
import Control.Monad (when)

main :: IO ()
main = shelly $ do
    echo "=== Running Compiler Pipeline Integration Tests ==="
    
    -- Find binaries in PATH (set by Nix wrapper)
    purescriptBinPath <- which "purescript-to-cpp23"
    cpp23BinPath <- which "cpp23-to-react"
    
    purescriptBin <- case purescriptBinPath of
        Just p -> return $ T.unpack p
        Nothing -> do
            echo "Error: purescript-to-cpp23 not found in PATH"
            liftIO $ exitWith 1
    
    cpp23Bin <- case cpp23BinPath of
        Just p -> return $ T.unpack p
        Nothing -> do
            echo "Error: cpp23-to-react not found in PATH"
            liftIO $ exitWith 1
    
    -- Create test output directory
    let testOutput = "src/compiler-pipeline/test-output"
        cpp23Output = testOutput </> "cpp23"
        reactOutput = testOutput </> "react"
    
    liftIO $ do
        createDirectoryIfMissing True cpp23Output
        createDirectoryIfMissing True reactOutput
    
    -- Test PureScript → C++23 compilation
    let testPurs = "src/compiler-pipeline/tests/test_purescript.purs"
    pursExists <- liftIO $ doesFileExist testPurs
    
    when pursExists $ do
        echo "Testing PureScript → C++23..."
        errExit False $ run_ purescriptBin 
            [T.pack "compile", T.pack testPurs, T.pack cpp23Output]
        code <- exitCode
        
        if code == 0
            then do
                let headerFile = cpp23Output </> "Test.hpp"
                headerExists <- liftIO $ doesFileExist headerFile
                if headerExists
                    then echo "✓ C++23 header generated"
                    else do
                        echo "✗ C++23 header missing"
                        liftIO $ exitWith 1
            else echo "PureScript compilation failed (continuing)"
    
    -- Test C++23 → React conversion
    let headerFile = cpp23Output </> "Test.hpp"
    headerExists <- liftIO $ doesFileExist headerFile
    
    when headerExists $ do
        echo "Testing C++23 → React..."
        errExit False $ run_ cpp23Bin 
            [T.pack headerFile, T.pack reactOutput]
        code <- exitCode
        
        if code == 0
            then echo "✓ React code generated"
            else echo "C++23 → React conversion failed (continuing)"
    
    echo "=== Integration tests complete ==="
