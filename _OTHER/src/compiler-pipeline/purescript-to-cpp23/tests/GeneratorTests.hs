{-# LANGUAGE OverloadedStrings #-}
module Main where

import Test.Hspec
import qualified Data.Text as T
import Parser (parseModule)
import Cpp23Generator (generateCpp23Header, generateCpp23Impl)

main :: IO ()
main = hspec $ do
  describe "C++23 Generator" $ do
    it "generates header for simple module" $ do
      let input = "module Test where\nx = 42;"
      case parseModule input of
        Right module' -> do
          let header = generateCpp23Header module'
          header `shouldContain` "#pragma once"
          header `shouldContain` "namespace"
          header `shouldContain` "Test"
        Left err -> expectationFailure $ "Parse error: " ++ show err
    
    it "generates implementation for simple module" $ do
      let input = "module Test where\nx = 42;"
      case parseModule input of
        Right module' -> do
          let impl = generateCpp23Impl module'
          impl `shouldContain` "#include"
          impl `shouldContain` "namespace"
        Left err -> expectationFailure $ "Parse error: " ++ show err
    
    it "generates correct C++ types" $ do
      let input = "module Test where\nx :: Int;\nx = 42;"
      case parseModule input of
        Right module' -> do
          let header = generateCpp23Header module'
          header `shouldContain` "std::int64_t"
        Left err -> expectationFailure $ "Parse error: " ++ show err
    
    it "generates function declarations" $ do
      let input = "module Test where\nf x = x + 1;"
      case parseModule input of
        Right module' -> do
          let header = generateCpp23Header module'
          header `shouldContain` "auto"
          header `shouldContain` "f"
        Left err -> expectationFailure $ "Parse error: " ++ show err
