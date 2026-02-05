{-|
Module      : Sidepanel.Components.CodeReview.CodeReviewTypes
Description : Types for proactive code review system
Types for automated code review, security analysis, and quality checks.
-}
module Sidepanel.Components.CodeReview.CodeReviewTypes where

import Prelude

-- | Code review issue
type CodeReviewIssue =
  { severity :: Severity
  , category :: IssueCategory
  , message :: String
  , location :: Location
  , suggestion :: Maybe String
  , fix :: Maybe CodeFix
  , rule :: String
  , confidence :: Number  -- 0.0 to 1.0
  }

-- | Severity level
data Severity
  = Critical
  | Major
  | Minor
  | Info

derive instance eqSeverity :: Eq Severity
derive instance ordSeverity :: Ord Severity

-- | Issue category
data IssueCategory
  = SecurityIssue
  | PerformanceIssue
  | QualityIssue
  | StyleIssue
  | BestPracticeIssue

derive instance eqIssueCategory :: Eq IssueCategory

-- | Location in code
type Location =
  { file :: String
  , line :: Int
  , column :: Int
  , endLine :: Int
  , endColumn :: Int
  }

-- | Code fix
type CodeFix =
  { range :: { start :: Location, end :: Location }
  , replacement :: String
  , description :: String
  , autoApplicable :: Boolean
  }

-- | Code review result
type CodeReviewResult =
  { file :: String
  , issues :: Array CodeReviewIssue
  , score :: QualityScore
  , suggestions :: Array ImprovementSuggestion
  , duration :: Number  -- Milliseconds
  }

-- | Quality score
type QualityScore =
  { overall :: Number  -- 0.0 to 1.0
  , security :: Number
  , performance :: Number
  , maintainability :: Number
  , testCoverage :: Number
  }

-- | Improvement suggestion
type ImprovementSuggestion =
  { category :: IssueCategory
  , priority :: Int  -- 1-10, higher is more important
  , description :: String
  , impact :: String
  , effort :: String  -- "Low", "Medium", "High"
  }

-- | Security vulnerability type
data SecurityVulnerability
  = SQLInjection
  | XSS
  | CSRF
  | InsecureDeserialization
  | SSRF
  | CommandInjection
  | PathTraversal
  | InsecureRandom
  | HardcodedSecret
  | WeakEncryption
  | OtherSecurity String

derive instance eqSecurityVulnerability :: Eq SecurityVulnerability

-- | Performance issue type
data PerformanceIssue
  = NPlusOneQuery
  | InefficientAlgorithm
  | MemoryLeak
  | UnnecessaryRerender
  | LargeBundleSize
  | SlowAsyncOperation
  | OtherPerformance String

derive instance eqPerformanceIssue :: Eq PerformanceIssue
