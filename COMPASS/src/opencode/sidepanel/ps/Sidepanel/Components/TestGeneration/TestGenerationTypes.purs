{-|
Module      : Sidepanel.Components.TestGeneration.TestGenerationTypes
Description : Types for test generation

Types for generating unit tests, property tests, and integration tests from code.
-}
module Sidepanel.Components.TestGeneration.TestGenerationTypes where

import Prelude

-- | Test generation request
type TestGenerationRequest =
  { filePath :: String
  , functionName :: Maybe String  -- If Nothing, generate tests for all functions
  , testType :: TestType
  , language :: String
  }

-- | Test type
data TestType
  = UnitTest
  | PropertyTest
  | IntegrationTest
  | E2ETest

derive instance eqTestType :: Eq TestType

-- | Test generation result
type TestGenerationResult =
  { success :: Boolean
  , testFile :: String
  , tests :: Array Test
  , errors :: Array String
  }

-- | Generated test
type Test =
  { name :: String
  , code :: String
  , description :: String
  , testType :: TestType
  }

-- | Test case
type TestCase =
  { inputs :: Array String  -- Multiple inputs for function parameters
  , expectedOutput :: String
  , description :: String
  }

-- | Function signature for test generation
type FunctionSignature =
  { name :: String
  , parameters :: Array Parameter
  , returnType :: String
  , visibility :: Visibility
  }

-- | Parameter
type Parameter =
  { name :: String
  , type_ :: String
  }

-- | Visibility
data Visibility
  = Public
  | Private
  | Protected

derive instance eqVisibility :: Eq Visibility
