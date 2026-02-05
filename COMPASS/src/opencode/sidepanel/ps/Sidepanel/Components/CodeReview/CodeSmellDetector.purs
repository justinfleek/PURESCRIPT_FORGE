{-|
Module      : Sidepanel.Components.CodeReview.CodeSmellDetector
Description : Code smell detection (duplication, long methods, magic numbers)
Detects code smells using pattern matching and AST analysis.
-}
module Sidepanel.Components.CodeReview.CodeSmellDetector where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)
import Sidepanel.Components.CodeReview.CodeReviewTypes
  ( CodeReviewIssue
  , Severity(..)
  , IssueCategory(..)
  , Location
  )

-- | Detect code smells
detectCodeSmells :: String -> String -> Aff (Array CodeReviewIssue)
detectCodeSmells filePath content = do
  let duplicationIssues = detectDuplication filePath content
  let magicNumberIssues = detectMagicNumbers filePath content
  let longFunctionIssues = detectLongFunctions filePath content
  let longParameterListIssues = detectLongParameterLists filePath content
  let deadCodeIssues = detectDeadCode filePath content
  
  pure $ duplicationIssues <> magicNumberIssues <> longFunctionIssues <>
         longParameterListIssues <> deadCodeIssues

-- | Detect code duplication
detectDuplication :: String -> String -> Array CodeReviewIssue
detectDuplication filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  -- Simple duplication detection: find repeated line sequences
  let duplicates = findDuplicateSequences lines 3  -- Minimum 3 lines
  
  Array.mapMaybe (\(duplicate /\ locations) ->
    if Array.length locations > 1 then
      Just
        { severity: Minor
        , category: QualityIssue
        , message: "Code duplication detected: " <> show (Array.length locations) <> " similar blocks found"
        , location:
            { file: filePath
            , line: (fromMaybe 0 (Array.head locations)) + 1
            , column: 0
            , endLine: (fromMaybe 0 (Array.head locations)) + Array.length duplicate
            , endColumn: 0
            }
        , suggestion: Just "Extract duplicated code into a reusable function"
        , fix: Nothing
        , rule: "quality/duplication"
        , confidence: 0.7
        }
    else
      Nothing
  ) duplicates

-- | Find duplicate sequences of lines
findDuplicateSequences :: Array String -> Int -> Array (Array String /\ Array Int)
findDuplicateSequences lines minLength = do
  let sequences = Array.range 0 (Array.length lines - minLength) >>= \start ->
        let seq = Array.slice start (start + minLength) lines
        in if Array.length seq == minLength then [seq /\ start] else []
  
  -- Group by sequence content
  groupBySequence sequences

-- | Group sequences by content
groupBySequence :: Array (Array String /\ Int) -> Array (Array String /\ Array Int)
groupBySequence sequences = do
  let grouped = Array.foldl (\acc (seq /\ idx) ->
        let key = String.joinWith "\n" seq
            existing = Array.find (\(s /\ _) -> String.joinWith "\n" s == key) acc
        in
          case existing of
            Nothing -> acc <> [seq /\ [idx]]
            Just (s /\ indices) -> Array.map (\(s' /\ indices') ->
                if String.joinWith "\n" s' == key then
                  (s' /\ (indices' <> [idx]))
                else
                  (s' /\ indices')
              ) acc
      ) [] sequences
  
  Array.filter (\(_ /\ indices) -> Array.length indices > 1) grouped

-- | Detect magic numbers
detectMagicNumbers :: String -> String -> Array CodeReviewIssue
detectMagicNumbers filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  Array.concatMapWithIndex (\lineIdx line -> detectMagicNumbersInLine filePath lineIdx line) lines

-- | Detect magic numbers in a single line
detectMagicNumbersInLine :: String -> Int -> String -> Array CodeReviewIssue
detectMagicNumbersInLine filePath lineIdx line = do
  -- Pattern: Standalone numbers that aren't 0, 1, -1, or common constants
  -- Use regex-like pattern matching
  let numbers = extractNumbers line
  
  Array.mapMaybe (\num -> 
    if isMagicNumber num then
      Just
        { severity: Info
        , category: QualityIssue
        , message: "Magic number detected: " <> show num <> " - Consider using a named constant"
        , location:
            { file: filePath
            , line: lineIdx + 1
            , column: 0
            , endLine: lineIdx + 1
            , endColumn: String.length line
            }
        , suggestion: Just "Replace magic number with a named constant or configuration value"
        , fix: Nothing
        , rule: "quality/magic-number"
        , confidence: 0.6
        }
    else
      Nothing
  ) numbers

-- | Extract numbers from line
extractNumbers :: String -> Array Number
extractNumbers line = do
  -- Simplified: find standalone numbers (not part of identifiers)
  -- Would use proper regex/AST analysis
  let parts = String.split (String.Pattern " ") line
  Array.mapMaybe (\part ->
    case parseNumber part of
      Nothing -> Nothing
      Just num -> if isMagicNumber num then Just num else Nothing
  ) parts

-- | Parse number from string
parseNumber :: String -> Maybe Number
parseNumber str =
  let cleaned = String.trim str
      parsed = parseNumberFFI cleaned
  in
    if parsed == 0.0 && cleaned /= "0" && cleaned /= "0.0" && String.length cleaned > 0 then
      Nothing
    else
      Just parsed

-- | Check if number is a magic number
isMagicNumber :: Number -> Boolean
isMagicNumber num =
  -- Common constants are not magic numbers
  num /= 0.0 && num /= 1.0 && num /= -1.0 && num /= 2.0 && num /= 10.0 &&
  num /= 100.0 && num /= 1000.0 && num /= 24.0 && num /= 60.0 && num /= 3600.0 &&
  num /= 1024.0 && num /= 3.14159 && num /= 2.71828

-- | Detect long functions
detectLongFunctions :: String -> String -> Array CodeReviewIssue
detectLongFunctions filePath content = do
  let lines = String.split (String.Pattern "\n") content
  let functions = extractFunctions content
  
  Array.mapMaybe (\func -> analyzeFunctionLength filePath func) functions

-- | Extract functions from code
extractFunctions :: String -> Array { name :: String, startLine :: Int, endLine :: Int, body :: String }
extractFunctions content = do
  let lines = String.split (String.Pattern "\n") content
  
  -- Simple extraction: find function declarations
  Array.mapMaybeWithIndex (\lineIdx line ->
    if isFunctionStart line then
      let functionName = extractFunctionName line
          endLine = findFunctionEnd lines lineIdx
          body = String.joinWith "\n" (Array.slice lineIdx endLine lines)
      in
        Just
          { name: functionName
          , startLine: lineIdx
          , endLine: endLine
          , body: body
          }
    else
      Nothing
  ) lines

-- | Check if line is function start
isFunctionStart :: String -> Boolean
isFunctionStart line =
  String.contains (String.Pattern "function ") line ||
  String.contains (String.Pattern "const ") line && String.contains (String.Pattern "= (") line ||
  String.contains (String.Pattern "const ") line && String.contains (String.Pattern "= function") line ||
  String.contains (String.Pattern "export function") line ||
  String.contains (String.Pattern "export const") line && String.contains (String.Pattern "= (") line

-- | Extract function name
extractFunctionName :: String -> String
extractFunctionName line =
  -- Simplified extraction
  if String.contains (String.Pattern "function ") line then
    let parts = String.split (String.Pattern "function ") line
        namePart = fromMaybe "" (Array.index parts 1)
        name = String.takeWhile (\c -> c /= '(' && c /= ' ') namePart
    in
      name
  else if String.contains (String.Pattern "const ") line then
    let parts = String.split (String.Pattern "const ") line
        namePart = fromMaybe "" (Array.index parts 1)
        name = String.takeWhile (\c -> c /= '=' && c /= ' ') namePart
    in
      name
  else
    "anonymous"

-- | Find function end
findFunctionEnd :: Array String -> Int -> Int
findFunctionEnd lines startLine = do
  let remainingLines = Array.drop startLine lines
  let braceCount = 0
  findFunctionEndHelper remainingLines 0 0

-- | Helper to find function end
findFunctionEndHelper :: Array String -> Int -> Int -> Int
findFunctionEndHelper lines currentIdx braceCount = do
  case Array.index lines currentIdx of
    Nothing -> currentIdx
    Just line ->
      let openBraces = countOccurrences line "{"
          closeBraces = countOccurrences line "}"
          newBraceCount = braceCount + openBraces - closeBraces
      in
        if newBraceCount == 0 && currentIdx > 0 then
          currentIdx
        else
          findFunctionEndHelper lines (currentIdx + 1) newBraceCount

-- | Count occurrences
countOccurrences :: String -> String -> Int
countOccurrences str substr =
  let pattern = String.Pattern substr
  in
    String.split pattern str # Array.length # (_ - 1)

-- | Analyze function length
analyzeFunctionLength :: String -> { name :: String, startLine :: Int, endLine :: Int, body :: String } -> Maybe CodeReviewIssue
analyzeFunctionLength filePath func = do
  let lineCount = func.endLine - func.startLine
  
  if lineCount > 50 then
    Just
      { severity: Minor
      , category: QualityIssue
      , message: "Long function detected: " <> func.name <> " has " <> show lineCount <> " lines (recommended: <50)"
      , location:
          { file: filePath
          , line: func.startLine + 1
          , column: 0
          , endLine: func.endLine + 1
          , endColumn: 0
          }
      , suggestion: Just "Consider breaking this function into smaller, more focused functions"
      , fix: Nothing
      , rule: "quality/long-function"
      , confidence: 0.9
      }
  else
    Nothing

-- | Detect long parameter lists
detectLongParameterLists :: String -> String -> Array CodeReviewIssue
detectLongParameterLists filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  Array.mapMaybeWithIndex (\lineIdx line -> detectLongParameterListLine filePath lineIdx line) lines

-- | Detect long parameter list in a single line
detectLongParameterListLine :: String -> Int -> String -> Maybe CodeReviewIssue
detectLongParameterListLine filePath lineIdx line = do
  if isFunctionStart line then
    let params = extractParameters line
        paramCount = Array.length params
    in
      if paramCount > 5 then
        Just
          { severity: Info
          , category: QualityIssue
          , message: "Long parameter list: Function has " <> show paramCount <> " parameters (recommended: <5)"
          , location:
              { file: filePath
              , line: lineIdx + 1
              , column: 0
              , endLine: lineIdx + 1
              , endColumn: String.length line
              }
          , suggestion: Just "Consider using an options object or parameter object pattern"
          , fix: Nothing
          , rule: "quality/long-parameter-list"
          , confidence: 0.8
          }
      else
        Nothing
  else
    Nothing

-- | Extract parameters from function signature
extractParameters :: String -> Array String
extractParameters line = do
  -- Find parameter list between parentheses
  let openParen = String.indexOf (String.Pattern "(") line
  let closeParen = String.indexOf (String.Pattern ")") line
  
  case openParen, closeParen of
    Just start, Just end ->
      let paramStr = String.substring (start + 1) end line
          params = String.split (String.Pattern ",") paramStr
      in
        Array.map String.trim params
    _, _ -> []

-- | Detect dead code
detectDeadCode :: String -> String -> Array CodeReviewIssue
detectDeadCode filePath content = do
  -- Pattern: Unused functions, unreachable code, commented-out code blocks
  let lines = String.split (String.Pattern "\n") content
  
  let unreachableIssues = detectUnreachableCode filePath lines
  let commentedIssues = detectCommentedCode filePath lines
  
  unreachableIssues <> commentedIssues

-- | Detect unreachable code
detectUnreachableCode :: String -> Array String -> Array CodeReviewIssue
detectUnreachableCode filePath lines = do
  -- Pattern: Code after return statement in same block
  -- Simplified - would need proper control flow analysis
  []

-- | Detect commented-out code
detectCommentedCode :: String -> Array String -> Array CodeReviewIssue
detectCommentedCode filePath lines = do
  -- Pattern: Large blocks of commented code
  Array.mapMaybeWithIndex (\lineIdx line ->
    if String.contains (String.Pattern "//") line || String.contains (String.Pattern "/*") line then
      let codeLength = String.length (String.replace (String.Pattern "//") (String.Pattern "") line)
      in
        if codeLength > 20 then
          Just
            { severity: Info
            , category: QualityIssue
            , message: "Commented-out code detected: Consider removing or documenting why it's kept"
            , location:
                { file: filePath
                , line: lineIdx + 1
                , column: 0
                , endLine: lineIdx + 1
                , endColumn: String.length line
                }
            , suggestion: Just "Remove commented code or add explanation if it's needed for reference"
            , fix: Nothing
            , rule: "quality/commented-code"
            , confidence: 0.5
            }
        else
          Nothing
    else
      Nothing
  ) lines

-- | FFI for number parsing
foreign import parseNumberFFI :: String -> Number
