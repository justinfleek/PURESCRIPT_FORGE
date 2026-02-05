{-|
Module      : Sidepanel.Components.Metrics.CodeMetricsTypes
Description : Types for code metrics

Types for code metrics and analytics.
-}
module Sidepanel.Components.Metrics.CodeMetricsTypes where

import Prelude

-- | Code metrics
type CodeMetrics =
  { file :: String
  , complexity :: ComplexityMetrics
  , maintainability :: MaintainabilityMetrics
  , technicalDebt :: TechnicalDebtMetrics
  , testCoverage :: Number  -- 0.0 to 1.0
  , linesOfCode :: Int
  , cyclomaticComplexity :: Number
  , cognitiveComplexity :: Number
  }

-- | Complexity metrics
type ComplexityMetrics =
  { cyclomatic :: Number
  , cognitive :: Number
  , nestingDepth :: Int
  , averageFunctionComplexity :: Number
  }

-- | Maintainability metrics
type MaintainabilityMetrics =
  { maintainabilityIndex :: Number  -- 0.0 to 100.0
  , codeDuplication :: Number  -- Percentage
  , averageFunctionLength :: Number
  , commentRatio :: Number  -- Percentage
  }

-- | Technical debt metrics
type TechnicalDebtMetrics =
  { totalDebt :: Number  -- In hours
  , debtRatio :: Number  -- Percentage
  , remediationEffort :: Number  -- In hours
  , hotspots :: Array Hotspot
  }

-- | Hotspot (problematic area)
type Hotspot =
  { file :: String
  , line :: Int
  , severity :: String
  }

-- | File metrics
type FileMetrics =
  { file :: String
  , metrics :: CodeMetrics
  , churn :: Number  -- How often file changes
  , lastModified :: Number  -- Timestamp
  }
