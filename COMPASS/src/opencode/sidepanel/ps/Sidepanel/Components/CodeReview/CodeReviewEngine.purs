{-|
Module      : Sidepanel.Components.CodeReview.CodeReviewEngine
Description : Main code review engine combining security and quality analysis
Main engine that orchestrates security and quality analysis for proactive code review.
-}
module Sidepanel.Components.CodeReview.CodeReviewEngine where

import Prelude

import Data.Array as Array
import Effect.Aff (Aff, parallel, sequential)
import Sidepanel.Components.CodeReview.CodeReviewTypes
  ( CodeReviewResult
  , CodeReviewIssue
  , QualityScore
  , ImprovementSuggestion
  )
import Sidepanel.Components.CodeReview.SecurityAnalyzer (analyzeSecurity)
import Sidepanel.Components.CodeReview.QualityAnalyzer (analyzeQuality)
import Sidepanel.Components.CodeReview.PerformanceAnalyzer (analyzePerformance)

-- | Review code file
reviewCode :: String -> String -> Aff CodeReviewResult
reviewCode filePath content = do
  startTime <- liftEffect getCurrentTime
  
  -- Run security, quality, and performance analysis in parallel
  securityIssues <- analyzeSecurity filePath content
  qualityIssues <- analyzeQuality filePath content
  performanceIssues <- analyzePerformance filePath content
  
  let allIssues = securityIssues <> qualityIssues <> performanceIssues
  
  -- Calculate quality score
  let score = calculateQualityScore allIssues
  
  -- Generate improvement suggestions
  let suggestions = generateImprovementSuggestions allIssues
  
  endTime <- liftEffect getCurrentTime
  let duration = Number.fromInt (endTime - startTime)
  
  pure
    { file: filePath
    , issues: allIssues
    , score: score
    , suggestions: suggestions
    , duration: duration
    }

-- | Calculate quality score from issues
calculateQualityScore :: Array CodeReviewIssue -> QualityScore
calculateQualityScore issues = do
  let criticalIssues = Array.filter (\i -> i.severity == Critical) issues
  let majorIssues = Array.filter (\i -> i.severity == Major) issues
  let securityIssues = Array.filter (\i -> i.category == SecurityIssue) issues
  let performanceIssues = Array.filter (\i -> i.category == PerformanceIssue) issues
  
  -- Score starts at 1.0, deduct points for issues
  let baseScore = 1.0
  let criticalPenalty = Number.fromInt (Array.length criticalIssues) * 0.1
  let majorPenalty = Number.fromInt (Array.length majorIssues) * 0.05
  let minorPenalty = Number.fromInt (Array.length (Array.filter (\i -> i.severity == Minor) issues)) * 0.01
  
  let overallScore = max 0.0 (baseScore - criticalPenalty - majorPenalty - minorPenalty)
  
  -- Security score (more weight on security issues)
  let securityPenalty = Number.fromInt (Array.length securityIssues) * 0.15
  let securityScore = max 0.0 (baseScore - securityPenalty)
  
  -- Performance score
  let performancePenalty = Number.fromInt (Array.length performanceIssues) * 0.1
  let performanceScore = max 0.0 (baseScore - performancePenalty)
  
  -- Maintainability score (based on quality issues)
  let qualityIssues = Array.filter (\i -> i.category == QualityIssue) issues
  let maintainabilityPenalty = Number.fromInt (Array.length qualityIssues) * 0.05
  let maintainabilityScore = max 0.0 (baseScore - maintainabilityPenalty)
  
  -- Test coverage (would be calculated from actual coverage data)
  let testCoverage = 0.8  -- Placeholder
  
  { overall: overallScore
  , security: securityScore
  , performance: performanceScore
  , maintainability: maintainabilityScore
  , testCoverage: testCoverage
  }

-- | Generate improvement suggestions
generateImprovementSuggestions :: Array CodeReviewIssue -> Array ImprovementSuggestion
generateImprovementSuggestions issues = do
  -- Group issues by category and generate high-level suggestions
  let securityIssues = Array.filter (\i -> i.category == SecurityIssue) issues
  let performanceIssues = Array.filter (\i -> i.category == PerformanceIssue) issues
  let qualityIssues = Array.filter (\i -> i.category == QualityIssue) issues
  
  let securitySuggestion = if Array.length securityIssues > 0 then
    Just
      { category: SecurityIssue
      , priority: 10  -- Highest priority
      , description: "Address " <> show (Array.length securityIssues) <> " security vulnerabilities"
      , impact: "Critical: Security vulnerabilities pose significant risk"
      , effort: "Medium"
      }
  else
    Nothing
  
  let performanceSuggestion = if Array.length performanceIssues > 0 then
    Just
      { category: PerformanceIssue
      , priority: 7
      , description: "Optimize " <> show (Array.length performanceIssues) <> " performance issues"
      , impact: "High: Performance issues affect user experience"
      , effort: "High"
      }
  else
    Nothing
  
  let qualitySuggestion = if Array.length qualityIssues > 0 then
    Just
      { category: QualityIssue
      , priority: 5
      , description: "Improve code quality: " <> show (Array.length qualityIssues) <> " issues found"
      , impact: "Medium: Code quality affects maintainability"
      , effort: "Medium"
      }
  else
    Nothing
  
  catMaybes [securitySuggestion, performanceSuggestion, qualitySuggestion]
  
-- | Import catMaybes
import Data.Array (catMaybes)

-- | Import utilities
import Effect.Class (liftEffect)
import Data.Maybe (Maybe(..))
import Sidepanel.Components.CodeReview.CodeReviewTypes (IssueCategory(..), PerformanceIssue(..), Severity(..))
import Sidepanel.Components.CodeReview.CodeReviewFFI (getCurrentTime)

-- | Import Data.Array.catMaybes
import Data.Array (catMaybes) as Array
