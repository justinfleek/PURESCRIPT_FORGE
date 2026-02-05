{-|
Module      : Sidepanel.Components.Refactoring.RefactoringTypes
Description : Types for refactoring assistance
Types for refactoring operations like extract method, rename symbol, move code, etc.
-}
module Sidepanel.Components.Refactoring.RefactoringTypes where

import Prelude

-- | Refactoring operation
data RefactoringOperation
  = ExtractMethod ExtractMethodParams
  | RenameSymbol RenameSymbolParams
  | MoveCode MoveCodeParams
  | InlineVariable InlineVariableParams
  | ExtractVariable ExtractVariableParams
  | SimplifyExpression SimplifyExpressionParams

derive instance eqRefactoringOperation :: Eq RefactoringOperation

-- | Extract method parameters
type ExtractMethodParams =
  { filePath :: String
  , range :: CodeRange
  , methodName :: String
  , parameters :: Array String
  , returnType :: Maybe String
  }

-- | Rename symbol parameters
type RenameSymbolParams =
  { filePath :: String
  , symbolName :: String
  , newName :: String
  , scope :: SymbolScope
  }

-- | Symbol scope
data SymbolScope
  = LocalScope
  | FileScope
  | ProjectScope

derive instance eqSymbolScope :: Eq SymbolScope

-- | Move code parameters
type MoveCodeParams =
  { sourceFile :: String
  , sourceRange :: CodeRange
  , targetFile :: String
  , targetPosition :: Position
  }

-- | Inline variable parameters
type InlineVariableParams =
  { filePath :: String
  , variableName :: String
  , occurrences :: Array CodeRange
  }

-- | Extract variable parameters
type ExtractVariableParams =
  { filePath :: String
  , expression :: String
  , range :: CodeRange
  , variableName :: String
  , variableType :: Maybe String
  }

-- | Simplify expression parameters
type SimplifyExpressionParams =
  { filePath :: String
  , range :: CodeRange
  , expression :: String
  }

-- | Code range
type CodeRange =
  { start :: Position
  , end :: Position
  }

-- | Position
type Position =
  { line :: Int
  , column :: Int
  }

-- | Refactoring result
type RefactoringResult =
  { success :: Boolean
  , changes :: Array FileChange
  , errors :: Array String
  , warnings :: Array String
  }

-- | File change
type FileChange =
  { filePath :: String
  , range :: CodeRange
  , oldText :: String
  , newText :: String
  , changeType :: ChangeType
  }

-- | Change type
data ChangeType
  = Insertion
  | Deletion
  | Replacement

derive instance eqChangeType :: Eq ChangeType

-- | Refactoring preview
type RefactoringPreview =
  { operation :: RefactoringOperation
  , changes :: Array FileChange
  , affectedFiles :: Array String
  , estimatedImpact :: ImpactEstimate
  }

-- | Impact estimate
type ImpactEstimate =
  { filesAffected :: Int
  , linesChanged :: Int
  , symbolsAffected :: Int
  , riskLevel :: RiskLevel
  }

-- | Risk level
data RiskLevel
  = LowRisk
  | MediumRisk
  | HighRisk

derive instance eqRiskLevel :: Eq RiskLevel
