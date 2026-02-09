{-# LANGUAGE OverloadedStrings #-}

-- | Render Gateway Integration Test Runner
module Main where

import Test.Hspec
import Integration

main :: IO ()
main = hspec integrationTests
