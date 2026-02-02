{-# LANGUAGE OverloadedStrings #-}
module Main where

import Test.Hspec
import qualified Data.Text as T
import Parser (parseModule)
import TypeChecker (typeCheckModule)

main :: IO ()
main = hspec $ do
  describe "Type Checker" $ do
    it "type checks simple module" $ do
      let input = "module Test where\nx = 42;"
      case parseModule input of
        Right module' -> do
          case typeCheckModule module' of
            Right _ -> return ()
            Left err -> expectationFailure $ "Type error: " ++ T.unpack err
        Left err -> expectationFailure $ "Parse error: " ++ show err
    
    it "type checks module with annotation" $ do
      let input = "module Test where\nx :: Int;\nx = 42;"
      case parseModule input of
        Right module' -> do
          case typeCheckModule module' of
            Right _ -> return ()
            Left err -> expectationFailure $ "Type error: " ++ T.unpack err
        Left err -> expectationFailure $ "Parse error: " ++ show err
    
    it "rejects type mismatch" $ do
      let input = "module Test where\nx :: String;\nx = 42;"
      case parseModule input of
        Right module' -> do
          case typeCheckModule module' of
            Right _ -> expectationFailure "Should have failed type check"
            Left _ -> return ()
        Left err -> expectationFailure $ "Parse error: " ++ show err
