{-|
Module      : Sidepanel.Components.Refactoring.RefactoringPreview
Description : Preview refactoring changes before applying
Generates preview of refactoring changes to show user before applying.
-}
module Sidepanel.Components.Refactoring.RefactoringPreview where

import Prelude

import Data.Array as Array
import Effect.Aff (Aff)
import Sidepanel.Components.Refactoring.RefactoringTypes
  ( RefactoringOperation
  , RefactoringPreview
  , FileChange
  , ImpactEstimate
  , RiskLevel(..)
  )
import Sidepanel.Components.Refactoring.RefactoringEngine (executeRefactoring)

-- | Generate preview of refactoring
previewRefactoring :: RefactoringOperation -> Aff RefactoringPreview
previewRefactoring operation = do
  -- Execute refactoring in dry-run mode
  result <- executeRefactoring operation
  
  -- Calculate impact estimate
  let impact = calculateImpact result.changes
  
  -- Determine affected files
  let affectedFiles = Array.nub (Array.map _.filePath result.changes)
  
  pure
    { operation: operation
    , changes: result.changes
    , affectedFiles: affectedFiles
    , estimatedImpact: impact
    }

-- | Calculate impact estimate
calculateImpact :: Array FileChange -> ImpactEstimate
calculateImpact changes =
  let filesAffected = Array.length (Array.nub (Array.map _.filePath changes))
      linesChanged = Array.length changes  -- Simplified
      symbolsAffected = filesAffected  -- Simplified
      riskLevel = determineRiskLevel changes
  in
    { filesAffected: filesAffected
    , linesChanged: linesChanged
    , symbolsAffected: symbolsAffected
    , riskLevel: riskLevel
    }

-- | Determine risk level
determineRiskLevel :: Array FileChange -> RiskLevel
determineRiskLevel changes =
  let fileCount = Array.length (Array.nub (Array.map _.filePath changes))
      changeCount = Array.length changes
  in
    if fileCount > 10 || changeCount > 50 then
      HighRisk
    else if fileCount > 3 || changeCount > 20 then
      MediumRisk
    else
      LowRisk
