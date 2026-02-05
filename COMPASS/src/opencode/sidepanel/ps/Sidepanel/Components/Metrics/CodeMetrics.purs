{-|
Module      : Sidepanel.Components.Metrics.CodeMetrics
Description : Code metrics and analytics

Calculates code complexity, maintainability index, technical debt, and other metrics.
-}
module Sidepanel.Components.Metrics.CodeMetrics where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)
import Sidepanel.Components.Metrics.CodeMetricsTypes
  ( CodeMetrics
  , ComplexityMetrics
  , MaintainabilityMetrics
  , TechnicalDebtMetrics
  , FileMetrics
  )

-- | Calculate code metrics for file
calculateMetrics :: String -> String -> Aff CodeMetrics
calculateMetrics filePath content = do
  let complexity = calculateComplexityMetrics content
  let maintainability = calculateMaintainabilityMetrics content
  let technicalDebt = calculateTechnicalDebtMetrics content
  let testCoverage = 0.0  -- Would calculate from test coverage data
  
  pure
    { file: filePath
    , complexity: complexity
    , maintainability: maintainability
    , technicalDebt: technicalDebt
    , testCoverage: testCoverage
    , linesOfCode: calculateLinesOfCode content
    , cyclomaticComplexity: calculateCyclomaticComplexity content
    , cognitiveComplexity: calculateCognitiveComplexity content
    }

-- | Calculate complexity metrics
calculateComplexityMetrics :: String -> ComplexityMetrics
calculateComplexityMetrics content =
  { cyclomatic: calculateCyclomaticComplexity content
  , cognitive: calculateCognitiveComplexity content
  , nestingDepth: calculateNestingDepth content
  , averageFunctionComplexity: calculateAverageFunctionComplexity content
  }

-- | Calculate cyclomatic complexity
calculateCyclomaticComplexity :: String -> Number
calculateCyclomaticComplexity content =
  let ifCount = countOccurrences content "if"
      whileCount = countOccurrences content "while"
      forCount = countOccurrences content "for"
      caseCount = countOccurrences content "case"
      catchCount = countOccurrences content "catch"
      andCount = countOccurrences content "&&"
      orCount = countOccurrences content "||"
      ternaryCount = countOccurrences content "?"
  in
    Number.fromInt (1 + ifCount + whileCount + forCount + caseCount + catchCount + andCount + orCount + ternaryCount)

-- | Calculate cognitive complexity
calculateCognitiveComplexity :: String -> Number
calculateCognitiveComplexity content =
  -- Cognitive complexity penalizes nested structures more
  let baseComplexity = calculateCyclomaticComplexity content
      nestingPenalty = Number.fromInt (calculateNestingDepth content) * 2.0
  in
    baseComplexity + nestingPenalty

-- | Calculate nesting depth
calculateNestingDepth :: String -> Int
calculateNestingDepth content =
  let lines = String.split (String.Pattern "\n") content
      maxDepth = Array.foldl (\maxDepth line ->
        let depth = calculateLineDepth line
        in
          if depth > maxDepth then depth else maxDepth
      ) 0 lines
  in
    maxDepth

-- | Calculate depth of a line
calculateLineDepth :: String -> Int
calculateLineDepth line =
  let indent = String.length (String.takeWhile (\c -> c == ' ' || c == '\t') line)
      openBraces = countOccurrences line "{"
      closeBraces = countOccurrences line "}"
  in
    indent / 2 + openBraces - closeBraces

-- | Calculate average function complexity
calculateAverageFunctionComplexity :: String -> Number
calculateAverageFunctionComplexity content =
  let functions = extractFunctions content
      totalComplexity = Array.foldl (\sum func -> sum + calculateCyclomaticComplexity func.body) 0.0 functions
      functionCount = Number.fromInt (Array.length functions)
  in
    if functionCount > 0.0 then
      totalComplexity / functionCount
    else
      0.0

-- | Extract functions from code
extractFunctions :: String -> Array { name :: String, body :: String }
extractFunctions content = do
  -- Simplified - would use proper AST parsing
  []

-- | Calculate maintainability metrics
calculateMaintainabilityMetrics :: String -> MaintainabilityMetrics
calculateMaintainabilityMetrics content =
  { maintainabilityIndex: calculateMaintainabilityIndex content
  , codeDuplication: calculateDuplicationPercentage content
  , averageFunctionLength: calculateAverageFunctionLength content
  , commentRatio: calculateCommentRatio content
  }

-- | Calculate maintainability index
calculateMaintainabilityIndex :: String -> Number
calculateMaintainabilityIndex content =
  -- MI = 171 - 5.2 * ln(Halstead Volume) - 0.23 * (Cyclomatic Complexity) - 16.2 * ln(Lines of Code)
  let halsteadVolume = calculateHalsteadVolume content
      cyclomaticComplexity = calculateCyclomaticComplexity content
      linesOfCode = Number.fromInt (calculateLinesOfCode content)
      mi = 171.0 - 5.2 * (Math.log halsteadVolume) - 0.23 * cyclomaticComplexity - 16.2 * (Math.log linesOfCode)
  in
    Math.max 0.0 (Math.min 100.0 mi)  -- Clamp between 0 and 100

-- | Calculate Halstead volume
calculateHalsteadVolume :: String -> Number
calculateHalsteadVolume content =
  -- Simplified Halstead metrics
  let operators = countOccurrences content "+" + countOccurrences content "-" +
                  countOccurrences content "*" + countOccurrences content "/" +
                  countOccurrences content "=" + countOccurrences content "=="
      operands = countOccurrences content "(" + countOccurrences content ")"
      volume = if operators + operands > 0 then
            Number.fromInt (operators + operands) * Math.log (Number.fromInt (operators + operands))
          else
            1.0
  in
    volume

-- | Calculate duplication percentage
calculateDuplicationPercentage :: String -> Number
calculateDuplicationPercentage content =
  -- Would use proper duplication detection
  -- For now, return placeholder
  0.0

-- | Calculate average function length
calculateAverageFunctionLength :: String -> Number
calculateAverageFunctionLength content =
  let functions = extractFunctions content
      totalLength = Array.foldl (\sum func -> sum + Number.fromInt (String.length func.body)) 0.0 functions
      functionCount = Number.fromInt (Array.length functions)
  in
    if functionCount > 0.0 then
      totalLength / functionCount
    else
      0.0

-- | Calculate comment ratio
calculateCommentRatio :: String -> Number
calculateCommentRatio content =
  let lines = String.split (String.Pattern "\n") content
      commentLines = Array.filter (\line ->
        String.contains (String.Pattern "//") line ||
        String.contains (String.Pattern "/*") line ||
        String.contains (String.Pattern "*") line
      ) lines
      totalLines = Array.length lines
      commentCount = Number.fromInt (Array.length commentLines)
      totalCount = Number.fromInt totalLines
  in
    if totalCount > 0.0 then
      (commentCount / totalCount) * 100.0
    else
      0.0

-- | Calculate technical debt metrics
calculateTechnicalDebtMetrics :: String -> TechnicalDebtMetrics
calculateTechnicalDebtMetrics content =
  { totalDebt: calculateTotalDebt content
  , debtRatio: calculateDebtRatio content
  , remediationEffort: calculateRemediationEffort content
  , hotspots: identifyHotspots content
  }

-- | Calculate total technical debt
calculateTotalDebt :: String -> Number
calculateTotalDebt content =
  -- Technical debt in hours
  let complexityDebt = calculateCyclomaticComplexity content * 0.5
      duplicationDebt = calculateDuplicationPercentage content * 2.0
      maintainabilityDebt = (100.0 - calculateMaintainabilityIndex content) * 0.1
  in
    complexityDebt + duplicationDebt + maintainabilityDebt

-- | Calculate debt ratio
calculateDebtRatio :: String -> Number
calculateDebtRatio content =
  let totalDebt = calculateTotalDebt content
      developmentCost = Number.fromInt (calculateLinesOfCode content) * 0.1
  in
    if developmentCost > 0.0 then
      (totalDebt / developmentCost) * 100.0
    else
      0.0

-- | Calculate remediation effort
calculateRemediationEffort :: String -> Number
calculateRemediationEffort content =
  -- Effort in hours to fix technical debt
  calculateTotalDebt content * 1.5

-- | Identify hotspots (problematic areas)
identifyHotspots :: String -> Array { file :: String, line :: Int, severity :: String }
identifyHotspots content = do
  -- Would identify complex, frequently changed areas
  []

-- | Calculate lines of code
calculateLinesOfCode :: String -> Int
calculateLinesOfCode content =
  let lines = String.split (String.Pattern "\n") content
      nonEmptyLines = Array.filter (\line -> String.length (String.trim line) > 0) lines
  in
    Array.length nonEmptyLines

-- | Count occurrences
countOccurrences :: String -> String -> Int
countOccurrences str substr =
  let pattern = String.Pattern substr
  in
    String.split pattern str # Array.length # (_ - 1)

-- | Import Math
import Data.Number as Number
import Math as Math
