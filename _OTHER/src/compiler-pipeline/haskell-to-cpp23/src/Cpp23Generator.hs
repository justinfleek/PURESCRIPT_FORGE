{-# LANGUAGE OverloadedStrings #-}
module Cpp23Generator where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import CoreParser
import TypeClassParser
import Runtime
import GHC.Core
import GHC.Core.DataCon
import GHC.Types.Var

-- | Generate C++23 from GHC Core with type classes and runtime
generateCpp23FromCore :: [CoreBind] -> T.Text
generateCpp23FromCore binds = T.unlines
  [ "#include <string>"
  , "#include <vector>"
  , "#include <optional>"
  , "#include <variant>"
  , "#include <functional>"
  , "#include <future>"
  , "#include <concepts>"
  , "#include <memory>"
  , "#include <thread>"
  , ""
  , "// Haskell Runtime Library"
  , generateRuntime
  , ""
  , "namespace generated {"
  , ""
  , "// Type class concepts"
  , T.unlines (map generateConcept (extractTypeClasses binds))
  , ""
  , "// Generated bindings"
  , T.unlines (map generateBinding binds)
  , ""
  , "} // namespace generated"
  ]

-- | Generate C++23 from Core binding
generateBinding :: CoreBind -> T.Text
generateBinding (NonRec var expr) =
  "auto " <> varToCpp var <> "() {\n" <>
  "  return " <> coreToCpp23 expr <> ";\n" <>
  "}\n"
generateBinding (Rec pairs) =
  T.unlines (map (\(var, expr) ->
    "auto " <> varToCpp var <> "() {\n" <>
    "  return " <> coreToCpp23 expr <> ";\n" <>
    "}\n"
    ) pairs)

varToCpp :: Var -> T.Text
varToCpp = T.pack . show . varName
