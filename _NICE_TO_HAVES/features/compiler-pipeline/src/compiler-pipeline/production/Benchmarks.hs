{-# LANGUAGE OverloadedStrings #-}
-- Phase 8: Performance Benchmarks
module Benchmarks where

import qualified Data.Text as T
import qualified System.CPUTime as CPU
import qualified Criterion.Main as Criterion
import Parser (PSModule(..), parseModule)
import TypeChecker (typeCheckModule)
import Cpp23Generator (generateCpp23Header, generateCpp23Impl)
import Optimizer (optimizeModule)

-- | Run all benchmarks
runBenchmarks :: IO ()
runBenchmarks = Criterion.defaultMain
  [ Criterion.bgroup "Parser"
    [ Criterion.bench "parse-small" $ Criterion.nf parseSmallModule smallModule
    , Criterion.bench "parse-medium" $ Criterion.nf parseMediumModule mediumModule
    , Criterion.bench "parse-large" $ Criterion.nf parseLargeModule largeModule
    ]
  , Criterion.bgroup "TypeChecker"
    [ Criterion.bench "typecheck-small" $ Criterion.nf typeCheckSmall smallModuleAST
    , Criterion.bench "typecheck-medium" $ Criterion.nf typeCheckMedium mediumModuleAST
    ]
  , Criterion.bgroup "Generator"
    [ Criterion.bench "generate-small" $ Criterion.nf generateSmall smallModuleAST
    , Criterion.bench "generate-medium" $ Criterion.nf generateMedium mediumModuleAST
    ]
  , Criterion.bgroup "Optimizer"
    [ Criterion.bench "optimize-small" $ Criterion.nf optimizeSmall smallModuleAST
    , Criterion.bench "optimize-medium" $ Criterion.nf optimizeMedium mediumModuleAST
    ]
  ]

-- | Benchmark parsing
parseSmallModule :: T.Text -> PSModule
parseSmallModule content = case parseModule content of
  Right m -> m
  Left _ -> emptyModule

parseMediumModule :: T.Text -> PSModule
parseMediumModule = parseSmallModule

parseLargeModule :: T.Text -> PSModule
parseLargeModule = parseSmallModule

-- | Benchmark type checking
typeCheckSmall :: PSModule -> PSModule
typeCheckSmall module' = case typeCheckModule module' of
  Right m -> m
  Left _ -> module'

typeCheckMedium :: PSModule -> PSModule
typeCheckMedium = typeCheckSmall

-- | Benchmark code generation
generateSmall :: PSModule -> T.Text
generateSmall module' = generateCpp23Header module' <> generateCpp23Impl module'

generateMedium :: PSModule -> T.Text
generateMedium = generateSmall

-- | Benchmark optimization
optimizeSmall :: PSModule -> PSModule
optimizeSmall = optimizeModule

optimizeMedium :: PSModule -> PSModule
optimizeMedium = optimizeModule

-- Test module data
smallModule :: T.Text
smallModule = "module Test where\nx = 42;"

mediumModule :: T.Text
mediumModule = T.unlines
  [ "module Test where"
  , "x = 42;"
  , "y = x + 1;"
  , "z = y * 2;"
  , "f a b = a + b;"
  , "g x = f x x;"
  , "data Maybe a = Nothing | Just a;"
  , "mapMaybe f Nothing = Nothing;"
  , "mapMaybe f (Just x) = Just (f x);"
  ]

smallModuleAST :: PSModule
smallModuleAST = case parseModule smallModule of
  Right m -> m
  Left _ -> emptyModule

mediumModuleAST :: PSModule
mediumModuleAST = case parseModule mediumModule of
  Right m -> m
  Left _ -> emptyModule

emptyModule :: PSModule
emptyModule = PSModule { moduleName = "", moduleExports = [], moduleImports = [], moduleDeclarations = [] }
