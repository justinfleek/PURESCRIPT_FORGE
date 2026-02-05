{-|
Module      : Sidepanel.Components.TestGeneration.TestGenerator
Description : Generate tests from code

Generates unit tests, property tests, and integration tests from code using AST analysis.
-}
module Sidepanel.Components.TestGeneration.TestGenerator where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.Either (Either(..))
import Effect.Aff (Aff)
import Tool.ASTEdit.FFI.FileIO (readFile, writeFile)
import Tool.ASTEdit.Structural
  ( AST
  , Node
  , NodeKind(..)
  , Symbol(..)
  )
import Tool.ASTEdit.Structural.Parser (parseToAST, getParser)
import Tool.ASTEdit.Structural.Transform.NodeOps (findNodesByKind, findNodesByPredicate)
import Tool.ASTEdit.Types (Span)
import Aleph.Coeffect.Spec (ASTLanguage(..))
import Data.String as String
import Sidepanel.Components.TestGeneration.TestGenerationTypes
  ( TestGenerationRequest
  , TestGenerationResult
  , Test
  , TestType(..)
  , TestCase
  , FunctionSignature
  , Parameter
  , Visibility(..)
  )

-- | Generate tests from request
generateTests :: TestGenerationRequest -> Aff TestGenerationResult
generateTests request = do
  -- 1. Read and parse source file
  readResult <- readFile request.filePath
  case readResult of
    Left err -> pure
      { success: false
      , testFile: generateTestFilePath request.filePath
      , tests: []
      , errors: ["Failed to read file: " <> err]
      }
    Right content -> do
      -- 2. Detect language and parse to AST
      let lang = detectLanguageFromPath request.filePath
      let parser = getParser lang
      parseResult <- parseToAST parser content
      case parseResult of
        Left parseErr -> pure
          { success: false
          , testFile: generateTestFilePath request.filePath
          , tests: []
          , errors: ["Parse error: " <> parseErr.message]
          }
        Right parsedAST -> do
          -- 3. Extract function signatures from AST
          let signatures = extractFunctionSignatures parsedAST.ast request.functionName
          
          -- 4. Generate tests based on type
          tests <- case request.testType of
            UnitTest -> generateUnitTestsFromAST request signatures parsedAST.ast
            PropertyTest -> generatePropertyTestsFromAST request signatures parsedAST.ast
            IntegrationTest -> generateIntegrationTestsFromAST request signatures
            E2ETest -> generateE2ETestsFromAST request signatures
          
          pure
            { success: true
            , testFile: generateTestFilePath request.filePath
            , tests: tests
            , errors: []
            }

-- | Detect language from file path
detectLanguageFromPath :: String -> ASTLanguage
detectLanguageFromPath filePath =
  if String.contains (String.Pattern ".purs") filePath then
    ASTPureScript
  else if String.contains (String.Pattern ".hs") filePath then
    ASTHaskell
  else if String.contains (String.Pattern ".lean") filePath then
    ASTLean4
  else if String.contains (String.Pattern ".ts") filePath || String.contains (String.Pattern ".tsx") filePath then
    ASTTypeScript
  else if String.contains (String.Pattern ".py") filePath then
    ASTPython
  else
    ASTUnknown filePath

-- | Generate unit tests from AST
generateUnitTestsFromAST :: TestGenerationRequest -> Array FunctionSignature -> AST -> Aff (Array Test)
generateUnitTestsFromAST request signatures ast = do
  Array.mapM (\signature -> do
    -- Generate test cases for this function
    let testCases = generateTestCasesForSignature signature
    
    -- Generate test code
    testCode <- generateUnitTestCodeForSignature request signature testCases
    
    pure
      { name: "test_" <> signature.name
      , code: testCode
      , description: "Generated unit test for " <> signature.name
      , testType: UnitTest
      }
  ) signatures

-- | Generate property tests from AST
generatePropertyTestsFromAST :: TestGenerationRequest -> Array FunctionSignature -> AST -> Aff (Array Test)
generatePropertyTestsFromAST request signatures ast = do
  Array.mapM (\signature -> do
    -- Generate property test code
    let propertyCode = generatePropertyTestCodeForSignature request signature
    
    pure
      { name: "prop_" <> signature.name
      , code: propertyCode
      , description: "Generated property test for " <> signature.name
      , testType: PropertyTest
      }
  ) signatures

-- | Generate integration tests from AST
generateIntegrationTestsFromAST :: TestGenerationRequest -> Array FunctionSignature -> Aff (Array Test)
generateIntegrationTestsFromAST request signatures = do
  -- Generate integration test that tests multiple functions together
  let integrationCode = generateIntegrationTestCodeForSignatures request signatures
  pure
    [ { name: "integration_test_" <> (fromMaybe "module" request.functionName)
      , code: integrationCode
      , description: "Generated integration test"
      , testType: IntegrationTest
      }
    ]

-- | Generate E2E tests from AST
generateE2ETestsFromAST :: TestGenerationRequest -> Array FunctionSignature -> Aff (Array Test)
generateE2ETestsFromAST request signatures = do
  let e2eCode = generateE2ETestCodeForSignatures request signatures
  pure
    [ { name: "e2e_test_" <> (fromMaybe "workflow" request.functionName)
      , code: e2eCode
      , description: "Generated E2E test"
      , testType: E2ETest
      }
    ]

-- | Generate property tests
generatePropertyTests :: TestGenerationRequest -> Array Test
generatePropertyTests request =
  [ { name: "prop_" <> (fromMaybe "function" request.functionName)
    , code: generatePropertyTestCode request
    , description: "Generated property test"
    , testType: PropertyTest
    }
  ]

-- | Generate integration tests
generateIntegrationTests :: TestGenerationRequest -> Array Test
generateIntegrationTests request =
  [ { name: "integration_test_" <> (fromMaybe "component" request.functionName)
    , code: generateIntegrationTestCode request
    , description: "Generated integration test"
    , testType: IntegrationTest
    }
  ]

-- | Generate E2E tests
generateE2ETests :: TestGenerationRequest -> Array Test
generateE2ETests request =
  [ { name: "e2e_test_" <> (fromMaybe "workflow" request.functionName)
    , code: generateE2ETestCode request
    , description: "Generated E2E test"
    , testType: E2ETest
    }
  ]

-- | Generate unit test code for signature
generateUnitTestCodeForSignature :: TestGenerationRequest -> FunctionSignature -> Array TestCase -> Aff String
generateUnitTestCodeForSignature request signature testCases = do
  case request.language of
    "purescript" -> pure (generatePureScriptTestCode request signature testCases)
    "haskell" -> pure (generateHaskellTestCode request signature testCases)
    "typescript" -> pure (generateTypeScriptTestCode request signature testCases)
    "python" -> pure (generatePythonTestCode request signature testCases)
    _ -> pure (generateGenericTestCode request signature testCases)

-- | Generate PureScript test code from signature and test cases
generatePureScriptTestCode :: TestGenerationRequest -> FunctionSignature -> Array TestCase -> String
generatePureScriptTestCode request signature testCases =
  let moduleName = extractModuleName request.filePath
      functionName = signature.name
      imports = "module Test." <> moduleName <> " where\n\n" <>
                "import Prelude\n" <>
                "import Test.Spec (describe, it)\n" <>
                "import Test.Spec.Assertions (shouldEqual)\n" <>
                "import " <> moduleName <> " (" <> functionName <> ")\n\n"
      
      testBody = Array.foldMap (\testCase ->
        "  it \"" <> testCase.description <> "\" do\n" <>
        "    " <> generatePureScriptAssertion functionName signature testCase <> "\n"
      ) testCases
      
      mockImports = if needsMocks signature then
        "\nimport Test.Spec.Mock (mock)\n"
      else
        ""
  in
    imports <> mockImports <>
    "spec = describe \"" <> functionName <> "\" do\n" <>
    testBody

-- | Check if function needs mocks
needsMocks :: FunctionSignature -> Boolean
needsMocks sig =
  -- Check if function has dependencies that need mocking
  -- For now, check if return type suggests side effects
  String.contains (String.Pattern "Aff") sig.returnType ||
  String.contains (String.Pattern "Effect") sig.returnType ||
  String.contains (String.Pattern "IO") sig.returnType

-- | Generate PureScript assertion
generatePureScriptAssertion :: String -> FunctionSignature -> TestCase -> String
generatePureScriptAssertion functionName signature testCase =
  let args = String.joinWith " " (Array.map showTestCaseValue testCase.inputs)
      expected = showTestCaseValue testCase.expectedOutput
      
      -- Handle Aff/Effect return types
      isAff = String.contains (String.Pattern "Aff") signature.returnType
      isEffect = String.contains (String.Pattern "Effect") signature.returnType
      
      assertion = if isAff || isEffect then
        -- For async functions, use Aff/Effect handling
        "result <- " <> functionName <> " " <> args <> "\n" <>
        "    result `shouldEqual` " <> expected
      else
        functionName <> " " <> args <> " `shouldEqual` " <> expected
  in
    assertion

-- | Generate test cases for function signature
generateTestCasesForSignature :: FunctionSignature -> Array TestCase
generateTestCasesForSignature sig =
  -- Generate multiple test cases: basic, edge cases, boundary cases
  [ { description: "basic case"
    , inputs: Array.map (\p -> generateDefaultValue p) sig.parameters
    , expectedOutput: generateDefaultValueForType sig.returnType
    }
  , { description: "edge case - empty/null values"
    , inputs: Array.map (\p -> generateEdgeCaseValue p) sig.parameters
    , expectedOutput: generateDefaultValueForType sig.returnType
    }
  , { description: "edge case - boundary values"
    , inputs: Array.map (\p -> generateBoundaryValue p) sig.parameters
    , expectedOutput: generateDefaultValueForType sig.returnType
    }
  ]

-- | Generate test cases with mocks
generateTestCasesWithMocks :: FunctionSignature -> Array TestCase
generateTestCasesWithMocks sig =
  -- Generate test cases that use mocks for dependencies
  Array.map (\testCase ->
    { description: testCase.description <> " (with mocks)"
    , inputs: Array.map (\input -> "mock_" <> input) testCase.inputs
    , expectedOutput: testCase.expectedOutput
    }
  ) (generateTestCasesForSignature sig)

-- | Generate default value for parameter
generateDefaultValue :: Parameter -> String
generateDefaultValue param = generateDefaultValueForType param.type_

-- | Generate default value for type string
generateDefaultValueForType :: String -> String
generateDefaultValueForType type_ = case type_ of
  "Int" -> "0"
  "Number" -> "0.0"
  "String" -> "\"test\""
  "Boolean" -> "true"
  "Array" -> "[]"
  "Maybe" -> "Nothing"
  "Either" -> "Left unit"
  "List" -> "Nil"
  _ -> "unit"

-- | Generate edge case value
generateEdgeCaseValue :: Parameter -> String
generateEdgeCaseValue param = generateEdgeCaseValueForType param.type_

-- | Generate edge case value for type
generateEdgeCaseValueForType :: String -> String
generateEdgeCaseValueForType type_ = case type_ of
  "Int" -> "-1"
  "Number" -> "NaN"
  "String" -> "\"\""
  "Boolean" -> "false"
  "Array" -> "[]"
  "Maybe" -> "Nothing"
  "Either" -> "Left unit"
  "List" -> "Nil"
  _ -> "unit"

-- | Generate boundary value
generateBoundaryValue :: Parameter -> String
generateBoundaryValue param = case param.type_ of
  "Int" -> "2147483647"  -- Max Int
  "Number" -> "Infinity"
  "String" -> "\"a\""  -- Single char
  "Boolean" -> "true"
  "Array" -> "[unit]"  -- Single element
  _ -> generateDefaultValue param

-- | Show test case value
showTestCaseValue :: String -> String
showTestCaseValue = identity

-- | Extract function signatures from AST
extractFunctionSignatures :: AST -> Maybe String -> Array FunctionSignature
extractFunctionSignatures ast functionNameM =
  -- Traverse AST to find all function declarations
  -- If functionName is provided, filter to that function only
  let allFunctions = findAllFunctionNodes ast
      filteredFunctions = case functionNameM of
        Nothing -> allFunctions
        Just name -> Array.filter (\sig -> sig.name == name) allFunctions
  in
    filteredFunctions

-- | Find all function nodes in AST
findAllFunctionNodes :: AST -> Array FunctionSignature
findAllFunctionNodes ast =
  -- Find all function declaration nodes
  let functionNodes = findNodesByKind ast FunctionDecl
      valueNodes = findNodesByKind ast ValueDecl  -- PureScript value declarations can be functions
      allNodes = functionNodes <> valueNodes
  in
    Array.mapMaybe extractFunctionSignatureFromNode allNodes

-- | Extract function signature from AST node
extractFunctionSignatureFromNode :: Node -> Maybe FunctionSignature
extractFunctionSignatureFromNode node =
  case node.kind of
    FunctionDecl -> Just
      { name: extractFunctionName node
      , parameters: extractParametersFromNode node
      , returnType: extractReturnTypeFromNode node
      , visibility: Public  -- Default to public, could inspect exports
      }
    ValueDecl -> 
      -- Check if value declaration is a function (has parameters or type arrow)
      if isFunctionValue node then
        Just
          { name: extractFunctionName node
          , parameters: extractParametersFromNode node
          , returnType: extractReturnTypeFromNode node
          , visibility: Public
          }
      else
        Nothing
    _ -> Nothing

-- | Check if value declaration is a function
isFunctionValue :: Node -> Boolean
isFunctionValue node =
  -- Check if node has type arrow (->) or lambda children
  Array.any (\child -> child.kind == TypeArrow || child.kind == Lambda) node.children ||
  -- Check if text contains "->" (type signature)
  String.contains (String.Pattern "->") node.text

-- | Extract function name from node
extractFunctionName :: Node -> String
extractFunctionName node =
  -- Try to find variable node in children (function name)
  case Array.find (\child -> child.kind == Variable) node.children of
    Just varNode -> varNode.text
    Nothing ->
      -- Fallback: extract from text (first word before space or =)
      let parts = String.split (String.Pattern " ") node.text
          firstPart = fromMaybe "" (Array.head parts)
          name = String.takeWhile (\c -> c /= ' ' && c /= '=' && c /= ':') firstPart
      in
        if name == "" then "unnamed" else name

-- | Extract parameters from function node
extractParametersFromNode :: Node -> Array Parameter
extractParametersFromNode node =
  -- Find parameter nodes in children
  -- Parameters can be Variable nodes, PatternVar nodes, or Lambda children
  let paramNodes = findParameterNodes node
  in
    Array.mapMaybe extractParameterFromNode paramNodes

-- | Find parameter nodes in function node
findParameterNodes :: Node -> Array Node
findParameterNodes node =
  -- Parameters are typically:
  -- 1. Direct children that are Variable or PatternVar
  -- 2. Children of Lambda nodes
  -- 3. Children before type annotation (TypeArrow)
  let directParams = Array.filter (\child -> 
        child.kind == Variable || 
        child.kind == PatternVar ||
        child.kind == PatternCon
      ) node.children
      
      lambdaParams = Array.concatMap (\child ->
        if child.kind == Lambda then
          Array.filter (\c -> c.kind == Variable || c.kind == PatternVar) child.children
        else
          []
      ) node.children
      
      -- Find type arrow to stop parameter extraction
      typeArrowIndex = Array.findIndex (\child -> child.kind == TypeArrow) node.children
      paramsBeforeType = case typeArrowIndex of
        Just idx -> Array.take idx node.children
        Nothing -> []
  in
    directParams <> lambdaParams <> paramsBeforeType

-- | Extract parameter from parameter node
extractParameterFromNode :: Node -> Maybe Parameter
extractParameterFromNode node =
  case node.kind of
    Variable -> Just
      { name: node.text
      , type_: "Unknown"  -- Type would need type inference
      }
    PatternVar -> Just
      { name: node.text
      , type_: "Unknown"
      }
    PatternCon -> Just
      { name: node.text
      , type_: "Unknown"
      }
    _ -> Nothing

-- | Extract return type from function node
extractReturnTypeFromNode :: Node -> String
extractReturnTypeFromNode node =
  -- Find type arrow node and extract right-hand side
  case Array.find (\child -> child.kind == TypeArrow) node.children of
    Just arrowNode ->
      -- Return type is typically the last child of arrow node
      case Array.last arrowNode.children of
        Just typeNode -> extractTypeFromNode typeNode
        Nothing -> "Unit"
    Nothing ->
      -- Check if node text contains type annotation
      if String.contains (String.Pattern "::") node.text then
        extractTypeFromText node.text
      else
        "Unit"

-- | Extract type from type node
extractTypeFromNode :: Node -> String
extractTypeFromNode node =
  case node.kind of
    TypeCon -> node.text
    TypeVar -> node.text
    TypeApp -> 
      -- Type application: extract constructor and arguments
      let con = case Array.head node.children of
            Just c -> extractTypeFromNode c
            Nothing -> ""
          args = Array.map extractTypeFromNode (Array.drop 1 node.children)
      in
        if Array.null args then con else con <> " " <> String.joinWith " " args
    TypeArrow ->
      -- Function type: extract return type (last child)
      case Array.last node.children of
        Just ret -> extractTypeFromNode ret
        Nothing -> "Unit"
    _ -> node.text

-- | Extract type from text (fallback)
extractTypeFromText :: String -> String
extractTypeFromText text =
  -- Look for ":: Type" pattern
  case String.indexOf (String.Pattern "::") text of
    Just idx ->
      let afterColon = String.drop (idx + 2) text
          typePart = String.takeWhile (\c -> c /= ' ' && c /= '=' && c /= '\n') afterColon
      in
        if typePart == "" then "Unit" else typePart
    Nothing -> "Unit"

-- | Fallback PureScript test generation
generatePureScriptUnitTestFallback :: TestGenerationRequest -> String
generatePureScriptUnitTestFallback request =
  "module Test." <> extractModuleName request.filePath <> " where\n\n" <>
  "import Prelude\n" <>
  "import Test.Spec (describe, it)\n" <>
  "import Test.Spec.Assertions (shouldEqual)\n\n" <>
  "spec = describe \"" <> (fromMaybe "Function" request.functionName) <> "\" do\n" <>
  "  it \"should work correctly\" do\n" <>
  "    -- TODO: Add test implementation\n" <>
  "    pure unit\n"

-- | Generate Haskell unit test
generateHaskellUnitTest :: TestGenerationRequest -> String
generateHaskellUnitTest request =
  "module Test." <> extractModuleName request.filePath <> " where\n\n" <>
  "import Test.Hspec\n\n" <>
  "spec :: Spec\n" <>
  "spec = describe \"" <> (fromMaybe "Function" request.functionName) <> "\" $ do\n" <>
  "  it \"should work correctly\" $ do\n" <>
  "    -- TODO: Add test implementation\n" <>
  "    pure ()\n"

-- | Generate TypeScript unit test
generateTypeScriptUnitTest :: TestGenerationRequest -> String
generateTypeScriptUnitTest request =
  "import { describe, it, expect } from 'vitest';\n\n" <>
  "describe('" <> (fromMaybe "Function" request.functionName) <> "', () => {\n" <>
  "  it('should work correctly', () => {\n" <>
  "    // TODO: Add test implementation\n" <>
  "    expect(true).toBe(true);\n" <>
  "  });\n" <>
  "});\n"

-- | Generate Python unit test
generatePythonUnitTest :: TestGenerationRequest -> String
generatePythonUnitTest request =
  "import unittest\n\n" <>
  "class Test" <> (fromMaybe "Function" request.functionName) <> "(unittest.TestCase):\n" <>
  "    def test_" <> (fromMaybe "function" request.functionName) <> "(self):\n" <>
  "        # TODO: Add test implementation\n" <>
  "        self.assertTrue(True)\n"

-- | Generate generic unit test
generateGenericUnitTest :: TestGenerationRequest -> String
generateGenericUnitTest request =
  "// Generated test for " <> (fromMaybe "function" request.functionName) <> "\n" <>
  "// TODO: Implement test\n"

-- | Generate property test code for signature
generatePropertyTestCodeForSignature :: TestGenerationRequest -> FunctionSignature -> String
generatePropertyTestCodeForSignature request signature =
  case request.language of
    "purescript" -> generatePureScriptPropertyTestForSignature request signature
    "haskell" -> generateHaskellPropertyTestForSignature request signature
    _ -> generateGenericPropertyTestForSignature request signature

-- | Generate PureScript property test for signature
generatePureScriptPropertyTestForSignature :: TestGenerationRequest -> FunctionSignature -> String
generatePureScriptPropertyTestForSignature request signature =
  let moduleName = extractModuleName request.filePath
      functionName = signature.name
      paramArbitraries = Array.map (\p -> generateArbitraryInstance p) signature.parameters
      propertyBody = generatePropertyBody signature
  in
    "module Test." <> moduleName <> " where\n\n" <>
    "import Prelude\n" <>
    "import Test.Spec.QuickCheck (quickCheck)\n" <>
    "import Test.QuickCheck (class Arbitrary, arbitrary)\n" <>
    "import " <> moduleName <> " (" <> functionName <> ")\n\n" <>
    String.joinWith "\n" paramArbitraries <>
    "\n" <>
    "prop_" <> functionName <> " :: Boolean\n" <>
    "prop_" <> functionName <> " = \n" <>
    "  quickCheck \\" <>
    String.joinWith " " (Array.map (\p -> p.name) signature.parameters) <>
    " ->\n" <>
    "    " <> propertyBody <> "\n"

-- | Generate Arbitrary instance for parameter
generateArbitraryInstance :: Parameter -> String
generateArbitraryInstance param =
  "instance arbitrary" <> String.toUpper (String.take 1 param.name) <> String.drop 1 param.name <>
  " :: Arbitrary " <> param.type_ <> " where\n" <>
  "  arbitrary = " <> generateArbitraryValue param.type_ <> "\n"

-- | Generate arbitrary value for type
generateArbitraryValue :: String -> String
generateArbitraryValue type_ = case type_ of
  "Int" -> "arbitrary"
  "Number" -> "arbitrary"
  "String" -> "arbitrary"
  "Boolean" -> "arbitrary"
  "Array" -> "arbitrary"
  _ -> "pure unit"

-- | Generate property body
generatePropertyBody :: FunctionSignature -> String
generatePropertyBody sig =
  -- Generate property that should hold for all inputs
  -- Common properties: idempotence, commutativity, associativity, etc.
  let functionCall = sig.name <> " " <> String.joinWith " " (Array.map (\p -> p.name) sig.parameters)
  in
    -- For now, generate a simple property
    "true  -- TODO: Add property (e.g., " <> functionCall <> " == " <> functionCall <> ")"

-- | Generate integration test code for signatures
generateIntegrationTestCodeForSignatures :: TestGenerationRequest -> Array FunctionSignature -> String
generateIntegrationTestCodeForSignatures request signatures =
  let moduleName = extractModuleName request.filePath
      testName = fromMaybe "Integration" request.functionName
  in
    "module Test." <> moduleName <> "Integration where\n\n" <>
    "import Prelude\n" <>
    "import Test.Spec (describe, it)\n" <>
    "import Test.Spec.Assertions (shouldEqual)\n" <>
    "import " <> moduleName <> "\n\n" <>
    "spec = describe \"" <> testName <> " Integration\" do\n" <>
    "  it \"should integrate multiple functions\" do\n" <>
    "    -- TODO: Add integration test implementation\n" <>
    "    pure unit\n"

-- | Generate E2E test code for signatures
generateE2ETestCodeForSignatures :: TestGenerationRequest -> Array FunctionSignature -> String
generateE2ETestCodeForSignatures request signatures =
  let moduleName = extractModuleName request.filePath
      testName = fromMaybe "E2E" request.functionName
  in
    "module Test." <> moduleName <> "E2E where\n\n" <>
    "import Prelude\n" <>
    "import Test.Spec (describe, it)\n" <>
    "import Test.Spec.Assertions (shouldEqual)\n" <>
    "import " <> moduleName <> "\n\n" <>
    "spec = describe \"" <> testName <> " E2E\" do\n" <>
    "  it \"should complete end-to-end workflow\" do\n" <>
    "    -- TODO: Add E2E test implementation\n" <>
    "    pure unit\n"

-- | Generate Haskell test code
generateHaskellTestCode :: TestGenerationRequest -> FunctionSignature -> Array TestCase -> String
generateHaskellTestCode request signature testCases =
  let moduleName = extractModuleName request.filePath
      functionName = signature.name
      testBody = Array.foldMap (\testCase ->
        "  it \"" <> testCase.description <> "\" $ do\n" <>
        "    " <> functionName <> " " <> String.joinWith " " testCase.inputs <>
        " `shouldBe` " <> testCase.expectedOutput <> "\n"
      ) testCases
  in
    "module Test." <> moduleName <> " where\n\n" <>
    "import Test.Hspec\n" <>
    "import " <> moduleName <> "\n\n" <>
    "spec :: Spec\n" <>
    "spec = describe \"" <> functionName <> "\" $ do\n" <>
    testBody

-- | Generate TypeScript test code
generateTypeScriptTestCode :: TestGenerationRequest -> FunctionSignature -> Array TestCase -> String
generateTypeScriptTestCode request signature testCases =
  let functionName = signature.name
      testBody = Array.foldMap (\testCase ->
        "  it('" <> testCase.description <> "', () => {\n" <>
        "    expect(" <> functionName <> "(" <> String.joinWith ", " testCase.inputs <> ")).toBe(" <>
        testCase.expectedOutput <> ");\n" <>
        "  });\n"
      ) testCases
  in
    "import { describe, it, expect } from 'vitest';\n" <>
    "import { " <> functionName <> " } from './" <> extractModuleName request.filePath <> "';\n\n" <>
    "describe('" <> functionName <> "', () => {\n" <>
    testBody <>
    "});\n"

-- | Generate Python test code
generatePythonTestCode :: TestGenerationRequest -> FunctionSignature -> Array TestCase -> String
generatePythonTestCode request signature testCases =
  let functionName = signature.name
      className = "Test" <> String.toUpper (String.take 1 functionName) <> String.drop 1 functionName
      testMethods = Array.mapWithIndex (\index testCase ->
        "    def test_" <> functionName <> "_" <> show index <> "(self):\n" <>
        "        result = " <> functionName <> "(" <> String.joinWith ", " testCase.inputs <> ")\n" <>
        "        self.assertEqual(result, " <> testCase.expectedOutput <> ")\n"
      ) testCases
  in
    "import unittest\n" <>
    "from " <> extractModuleName request.filePath <> " import " <> functionName <> "\n\n" <>
    "class " <> className <> "(unittest.TestCase):\n" <>
    String.joinWith "\n" testMethods

-- | Generate generic test code
generateGenericTestCode :: TestGenerationRequest -> FunctionSignature -> Array TestCase -> String
generateGenericTestCode request signature testCases =
  "// Generated test for " <> signature.name <> "\n" <>
  "// TODO: Implement test\n"

-- | Generate Haskell property test for signature
generateHaskellPropertyTestForSignature :: TestGenerationRequest -> FunctionSignature -> String
generateHaskellPropertyTestForSignature request signature =
  let moduleName = extractModuleName request.filePath
      functionName = signature.name
  in
    "module Test." <> moduleName <> " where\n\n" <>
    "import Test.QuickCheck\n" <>
    "import " <> moduleName <> "\n\n" <>
    "prop_" <> functionName <> " :: Property\n" <>
    "prop_" <> functionName <> " = \n" <>
    "  property $ \\" <>
    String.joinWith " " (Array.map (\p -> p.name) signature.parameters) <>
    " ->\n" <>
    "    -- TODO: Add property (e.g., " <> functionName <> " " <>
    String.joinWith " " (Array.map (\p -> p.name) signature.parameters) <>
    " == ...)\n" <>
    "    True\n"

-- | Generate generic property test for signature
generateGenericPropertyTestForSignature :: TestGenerationRequest -> FunctionSignature -> String
generateGenericPropertyTestForSignature request signature =
  "// Generated property test for " <> signature.name <> "\n" <>
  "// TODO: Implement property test\n"

-- | Generate test file path
generateTestFilePath :: String -> String
generateTestFilePath filePath =
  let basePath = String.dropSuffix (String.Pattern ".purs") filePath
      basePath' = String.dropSuffix (String.Pattern ".hs") basePath
      basePath'' = String.dropSuffix (String.Pattern ".ts") basePath'
      basePath''' = String.dropSuffix (String.Pattern ".py") basePath''
  in
    basePath''' <> "Test.purs"  -- Default to PureScript

-- | Extract module name from file path
extractModuleName :: String -> String
extractModuleName filePath =
  let parts = String.split (String.Pattern "/") filePath
      fileName = fromMaybe "" (Array.last parts)
      withoutExt = String.dropSuffix (String.Pattern ".purs") fileName
      withoutExt' = String.dropSuffix (String.Pattern ".hs") withoutExt
      withoutExt'' = String.dropSuffix (String.Pattern ".ts") withoutExt'
      withoutExt''' = String.dropSuffix (String.Pattern ".py") withoutExt''
  in
    withoutExt'''
