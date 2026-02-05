{-|
Module      : Sidepanel.Components.MultiFileContext.FileRelationshipTypes
Description : Types for multi-file context awareness
Types for cross-file understanding, import analysis, change impact analysis.
-}
module Sidepanel.Components.MultiFileContext.FileRelationshipTypes where

import Prelude

-- | File relationship
type FileRelationship =
  { file :: String
  , relationship :: RelationshipType
  , strength :: Number  -- 0.0 to 1.0, how strongly related
  , evidence :: Array Evidence
  }

-- | Relationship type
data RelationshipType
  = Imports  -- File imports symbols from this file
  | Exports  -- File exports symbols used by this file
  | Uses  -- File uses types/functions from this file
  | Tests  -- File contains tests for this file
  | Config  -- File is configuration for this file
  | Related  -- General relationship

derive instance eqRelationshipType :: Eq RelationshipType

-- | Evidence for relationship
type Evidence =
  { type_ :: EvidenceType
  , location :: Location
  , description :: String
  }

-- | Evidence type
data EvidenceType
  = ImportStatement
  | TypeReference
  | FunctionCall
  | TestFile
  | ConfigFile
  | SimilarName
  | SameDirectory

derive instance eqEvidenceType :: Eq EvidenceType

-- | Location in file
type Location =
  { file :: String
  , line :: Int
  , column :: Int
  }

-- | Import analysis
type ImportAnalysis =
  { file :: String
  , imports :: Array ImportInfo
  , exports :: Array ExportInfo
  , transitiveImports :: Array String  -- Files imported transitively
  }

-- | Import information
type ImportInfo =
  { module :: String
  , file :: String  -- Resolved file path
  , symbols :: Array String  -- Imported symbols
  , importType :: ImportType
  }

-- | Import type
data ImportType
  = NamedImport
  | NamespaceImport
  | DefaultImport
  | SideEffectImport

derive instance eqImportType :: Eq ImportType

-- | Export information
type ExportInfo =
  { symbol :: String
  , symbolType :: SymbolType
  , exportedAs :: String  -- May be different from symbol name
  }

-- | Symbol type
data SymbolType
  = FunctionSymbol
  | TypeSymbol
  | ValueSymbol
  | ClassSymbol
  | InterfaceSymbol

derive instance eqSymbolType :: Eq SymbolType

-- | Change impact analysis
type ChangeImpactAnalysis =
  { changedFile :: String
  , affectedFiles :: Array AffectedFile
  , breakingChanges :: Array BreakingChange
  , safeChanges :: Array SafeChange
  }

-- | Affected file
type AffectedFile =
  { file :: String
  , impact :: ImpactLevel
  , reason :: String
  , affectedSymbols :: Array String
  }

-- | Impact level
data ImpactLevel
  = HighImpact  -- Breaking change
  | MediumImpact  -- May break
  | LowImpact  -- Unlikely to break

derive instance eqImpactLevel :: Eq ImpactLevel

-- | Breaking change
type BreakingChange =
  { file :: String
  , symbol :: String
  , changeType :: BreakingChangeType
  , affectedFiles :: Array String
  }

-- | Breaking change type
data BreakingChangeType
  = RemovedSymbol
  | ChangedSignature
  | ChangedType
  | MovedSymbol

derive instance eqBreakingChangeType :: Eq BreakingChangeType

-- | Safe change
type SafeChange =
  { file :: String
  , symbol :: String
  , changeType :: SafeChangeType
  }

-- | Safe change type
data SafeChangeType
  = AddedSymbol
  | InternalRefactor
  | DocumentationChange

derive instance eqSafeChangeType :: Eq SafeChangeType

-- | Dependency graph
type DependencyGraph =
  { nodes :: Array FileNode
  , edges :: Array DependencyEdge
  }

-- | File node
type FileNode =
  { file :: String
  , type_ :: FileType
  , dependencies :: Int  -- Count of dependencies
  , dependents :: Int  -- Count of files depending on this
  }

-- | File type
data FileType
  = SourceFile
  | TestFile
  | ConfigFile
  | DocumentationFile

derive instance eqFileType :: Eq FileType

-- | Dependency edge
type DependencyEdge =
  { from :: String
  , to :: String
  , relationship :: RelationshipType
  , weight :: Number  -- Strength of dependency
  }
