{-|
Module      : Sidepanel.Components.MultiFileContext.ChangeImpactAnalyzer
Description : Analyze impact of code changes
Analyzes what files will be affected by changes to a file.
-}
module Sidepanel.Components.MultiFileContext.ChangeImpactAnalyzer where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Sidepanel.Components.MultiFileContext.FileRelationshipTypes
  ( ChangeImpactAnalysis
  , AffectedFile
  , ImpactLevel(..)
  , BreakingChange
  , BreakingChangeType(..)
  , SafeChange
  , SafeChangeType(..)
  )
import Sidepanel.Components.MultiFileContext.FileRelationshipAnalyzer (analyzeFileRelationships)

-- | Analyze impact of changes to a file
analyzeChangeImpact :: String -> Array String -> Aff ChangeImpactAnalysis
analyzeChangeImpact changedFile allFiles = do
  -- Get file relationships
  relationships <- analyzeFileRelationships changedFile allFiles
  
  -- Categorize affected files by impact level
  let affectedFiles = Array.map (\rel ->
        { file: rel.file
        , impact: determineImpact rel
        , reason: describeReason rel
        , affectedSymbols: extractAffectedSymbols rel
        }
      ) relationships
  
  -- Identify breaking changes
  let breakingChanges = identifyBreakingChanges changedFile relationships
  
  -- Identify safe changes
  let safeChanges = identifySafeChanges changedFile relationships
  
  pure
    { changedFile: changedFile
    , affectedFiles: affectedFiles
    , breakingChanges: breakingChanges
    , safeChanges: safeChanges
    }

-- | Determine impact level from relationship
determineImpact :: FileRelationship -> ImpactLevel
determineImpact rel =
  case rel.relationship of
    Exports -> HighImpact  -- Files importing this will break
    Uses -> MediumImpact  -- May break if types change
    Imports -> LowImpact  -- Less likely to break
    Tests -> LowImpact  -- Tests may need updates
    Config -> LowImpact  -- Config rarely breaks
    Related -> LowImpact

-- | Describe reason for impact
describeReason :: FileRelationship -> String
describeReason rel =
  case rel.relationship of
    Exports -> "Exports symbols used by this file"
    Uses -> "Uses types/functions from this file"
    Imports -> "Imports from this file"
    Tests -> "Contains tests for this file"
    Config -> "Configuration for this file"
    Related -> "Related file"

-- | Extract affected symbols from relationship
extractAffectedSymbols :: FileRelationship -> Array String
extractAffectedSymbols rel =
  -- Would extract from evidence
  []

-- | Identify breaking changes
identifyBreakingChanges :: String -> Array FileRelationship -> Array BreakingChange
identifyBreakingChanges changedFile relationships =
  -- Would analyze actual code changes to detect breaking changes
  -- For now, flag high-impact relationships as potential breaking changes
  Array.mapMaybe (\rel ->
    if rel.relationship == Exports && rel.strength > 0.7 then
      Just
        { file: changedFile
        , symbol: ""  -- Would extract from changes
        , changeType: ChangedSignature
        , affectedFiles: [rel.file]
        }
    else
      Nothing
  ) relationships

-- | Identify safe changes
identifySafeChanges :: String -> Array FileRelationship -> Array SafeChange
identifySafeChanges changedFile relationships =
  -- Would analyze changes to identify safe ones
  []
