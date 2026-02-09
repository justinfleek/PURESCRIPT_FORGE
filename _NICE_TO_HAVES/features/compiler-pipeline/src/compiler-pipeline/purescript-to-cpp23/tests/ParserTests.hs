{-# LANGUAGE OverloadedStrings #-}
module Main where

import Test.Hspec
import qualified Data.Text as T
import Parser (parseModule, PSModule(..))

main :: IO ()
main = hspec $ do
  describe "PureScript Parser" $ do
    it "parses simple module" $ do
      let input = "module Test where\nx = 42;"
      case parseModule input of
        Right (PSModule name _ _ decls) -> do
          name `shouldBe` "Test"
          length decls `shouldBe` 1
        Left err -> expectationFailure $ "Parse error: " ++ show err
    
    it "parses module with type annotation" $ do
      let input = "module Test where\nx :: Int;\nx = 42;"
      case parseModule input of
        Right (PSModule _ _ _ decls) -> length decls `shouldBe` 1
        Left err -> expectationFailure $ "Parse error: " ++ show err
    
    it "parses data declaration" $ do
      let input = "module Test where\ndata Maybe a = Nothing | Just a;"
      case parseModule input of
        Right (PSModule _ _ _ decls) -> length decls `shouldBe` 1
        Left err -> expectationFailure $ "Parse error: " ++ show err
    
    it "parses function application" $ do
      let input = "module Test where\nf x = x + 1;"
      case parseModule input of
        Right (PSModule _ _ _ decls) -> length decls `shouldBe` 1
        Left err -> expectationFailure $ "Parse error: " ++ show err
    
    it "parses lambda expression" $ do
      let input = "module Test where\nf = \\x -> x + 1;"
      case parseModule input of
        Right (PSModule _ _ _ decls) -> length decls `shouldBe` 1
        Left err -> expectationFailure $ "Parse error: " ++ show err
    
    it "parses case expression" $ do
      let input = "module Test where\nf x = case x of\n  Just y -> y;\n  Nothing -> 0;"
      case parseModule input of
        Right (PSModule _ _ _ decls) -> length decls `shouldBe` 1
        Left err -> expectationFailure $ "Parse error: " ++ show err
    
    it "rejects invalid syntax" $ do
      let input = "module Test where\nx ="
      case parseModule input of
        Right _ -> expectationFailure "Should have failed to parse"
        Left _ -> return ()
