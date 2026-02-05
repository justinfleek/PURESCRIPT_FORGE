{-|
Module      : Sidepanel.Components.SemanticCode.DependencyGraphTypes
Description : Types for dependency graph
Types for representing file dependencies and relationships.
-}
module Sidepanel.Components.SemanticCode.DependencyGraphTypes where

import Prelude

-- | Dependency graph
type DependencyGraph =
  { nodes :: Array FileNode
  , edges :: Array DependencyEdge
  , rootNodes :: Array FileNode  -- Files with no dependencies
  }

-- | File node in graph
type FileNode =
  { id :: String  -- File path
  , path :: String
  , name :: String  -- File name
  , imports :: Array String  -- Modules imported
  , exports :: Array String  -- Modules exported
  , type_ :: String  -- File type (purescript, haskell, etc.)
  , size :: Int  -- File size in bytes
  , complexity :: Number  -- Code complexity metric
  }

-- | Dependency edge
type DependencyEdge =
  { from :: String  -- Source file ID
  , to :: String  -- Target file ID
  , type_ :: EdgeType  -- Type of dependency
  , strength :: Number  -- Strength of dependency (0.0 to 1.0)
  , label :: String  -- Edge label (module name, etc.)
  }

-- | Edge type
data EdgeType
  = ImportEdge  -- File imports from another
  | ExportEdge  -- File exports to another
  | CallEdge  -- Function call relationship
  | TypeEdge  -- Type dependency
  | TestEdge  -- Test file relationship

derive instance eqEdgeType :: Eq EdgeType

-- | File relationship
data FileRelationship
  = Imports
  | Exports
  | Uses
  | Tests
  | Configures

derive instance eqFileRelationship :: Eq FileRelationship
