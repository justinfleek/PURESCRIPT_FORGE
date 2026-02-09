#!/usr/bin/env runghc
{-# LANGUAGE OverloadedStrings #-}

-- |
-- test-all: Run all compiler pipeline tests
--
-- Runs both unit and integration tests in sequence.

import Shelly (shelly, run_, echo)

main :: IO ()
main = shelly $ do
    echo "=== Full Compiler Pipeline Test Suite ==="
    
    -- Run unit tests
    echo "Running unit tests..."
    run_ "nix" ["run", ".#compiler-pipeline-test"]
    
    -- Run integration tests
    echo "Running integration tests..."
    run_ "nix" ["run", ".#compiler-pipeline-test-integration"]
    
    echo "=== All tests passed ==="
