{-|
Module      : Sidepanel.Components.CodeReview.QualityAnalyzer
Description : Code quality analysis (complexity, duplication, maintainability)
Analyzes code quality metrics: complexity, duplication, maintainability.
-}
module Sidepanel.Components.CodeReview.QualityAnalyzer where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)
import Sidepanel.Components.CodeReview.CodeReviewTypes
  ( CodeReviewIssue
  , PerformanceIssue(..)
  , Severity(..)
  , IssueCategory(..)
  , Location
  )

-- | Analyze code quality
analyzeQuality :: String -> String -> Aff (Array CodeReviewIssue)
analyzeQuality filePath content = do
  let complexityIssues = detectComplexity filePath content
  let maintainabilityIssues = detectMaintainabilityIssues filePath content
  
  -- Import code smell detector
  codeSmellIssues <- detectCodeSmells filePath content
  
  pure $ complexityIssues <> maintainabilityIssues <> codeSmellIssues

-- | Import code smell detector
import Sidepanel.Components.CodeReview.CodeSmellDetector (detectCodeSmells)

-- | Detect high complexity
detectComplexity :: String -> String -> Array CodeReviewIssue
detectComplexity filePath content = do
  let lines = String.split (String.Pattern "\n") content
  let functions = extractFunctions content
  
  Array.mapMaybe (\func -> analyzeFunctionComplexity filePath func) functions

-- | Extract functions from code (simplified)
extractFunctions :: String -> Array { name :: String, startLine :: Int, endLine :: Int, body :: String }
extractFunctions content = do
  -- Simplified - would use proper AST parsing
  []

-- | Analyze function complexity
analyzeFunctionComplexity :: String -> { name :: String, startLine :: Int, endLine :: Int, body :: String } -> Maybe CodeReviewIssue
analyzeFunctionComplexity filePath func = do
  -- Calculate cyclomatic complexity
  let complexity = calculateCyclomaticComplexity func.body
  
  if complexity > 10 then
    Just
      { severity: Minor
      , category: QualityIssue
      , message: "High cyclomatic complexity (" <> show complexity <> "): Function is difficult to understand and test"
      , location:
          { file: filePath
          , line: func.startLine
          , column: 0
          , endLine: func.endLine
          , endColumn: 0
          }
      , suggestion: Just "Consider breaking this function into smaller, more focused functions"
      , fix: Nothing
      , rule: "quality/high-complexity"
      , confidence: 0.8
      }
  else
    Nothing

-- | Calculate cyclomatic complexity (simplified)
calculateCyclomaticComplexity :: String -> Int
calculateCyclomaticComplexity body = do
  -- Count decision points: if, while, for, case, &&, ||, ?:
  let ifCount = countOccurrences body "if"
  let whileCount = countOccurrences body "while"
  let forCount = countOccurrences body "for"
  let caseCount = countOccurrences body "case"
  let andCount = countOccurrences body "&&"
  let orCount = countOccurrences body "||"
  let ternaryCount = countOccurrences body "?"
  
  -- Base complexity is 1, add decision points
  1 + ifCount + whileCount + forCount + caseCount + andCount + orCount + ternaryCount

-- | Count occurrences of substring
countOccurrences :: String -> String -> Int
countOccurrences str substr = do
  let pattern = String.Pattern substr
  String.split pattern str # Array.length # (_ - 1)

-- | Detect code duplication (moved to CodeSmellDetector)
detectDuplication :: String -> String -> Array CodeReviewIssue
detectDuplication filePath content = do
  -- Moved to CodeSmellDetector.detectCodeSmells
  []

-- | Detect maintainability issues
detectMaintainabilityIssues :: String -> String -> Array CodeReviewIssue
detectMaintainabilityIssues filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  let longLineIssues = Array.mapMaybeWithIndex (detectLongLine filePath) lines
  let magicNumberIssues = detectMagicNumbers filePath content
  let longFunctionIssues = detectLongFunctions filePath content
  
  longLineIssues <> magicNumberIssues <> longFunctionIssues

-- | Detect long lines
detectLongLine :: String -> Int -> String -> Maybe CodeReviewIssue
detectLongLine filePath lineIdx line = do
  if String.length line > 120 then
    Just
      { severity: Info
      , category: StyleIssue
      , message: "Line exceeds 120 characters: Consider breaking into multiple lines"
      , location:
          { file: filePath
          , line: lineIdx + 1
          , column: 0
          , endLine: lineIdx + 1
          , endColumn: String.length line
          }
      , suggestion: Just "Break long lines for better readability"
      , fix: Nothing
      , rule: "style/long-line"
      , confidence: 1.0
      }
  else
    Nothing

-- | Detect magic numbers (moved to CodeSmellDetector)
detectMagicNumbers :: String -> String -> Array CodeReviewIssue
detectMagicNumbers filePath content = do
  -- Moved to CodeSmellDetector.detectCodeSmells
  []

-- | Detect long functions (moved to CodeSmellDetector)
detectLongFunctions :: String -> String -> Array CodeReviewIssue
detectLongFunctions filePath content = do
  -- Moved to CodeSmellDetector.detectCodeSmells
  []

-- | Detect performance issues (moved to PerformanceAnalyzer)
detectPerformanceIssues :: String -> String -> Array CodeReviewIssue
detectPerformanceIssues filePath content = do
  -- Moved to PerformanceAnalyzer.analyzePerformance
  []

-- | Import performance analyzer
import Sidepanel.Components.CodeReview.PerformanceAnalyzer (analyzePerformance)
