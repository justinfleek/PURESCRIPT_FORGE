{-|
Module      : Sidepanel.Components.MultiFileContext.DependencyGraphBuilder
Description : Build dependency graph visualization
Builds a dependency graph for visualization.
-}
module Sidepanel.Components.MultiFileContext.DependencyGraphBuilder where

import Prelude

import Data.Array as Array
import Data.Map as Map
import Effect.Aff (Aff)
import Sidepanel.Components.MultiFileContext.FileRelationshipTypes
  ( DependencyGraph
  , FileNode
  , FileType(..)
  , DependencyEdge
  , RelationshipType(..)
  )
import Sidepanel.Components.MultiFileContext.FileRelationshipAnalyzer (analyzeFileRelationships)

-- | Build dependency graph for files
buildDependencyGraph :: Array String -> Aff DependencyGraph
buildDependencyGraph files = do
  -- Analyze relationships for all files
  allRelationships <- Array.concat <$> Array.traverse (\f -> analyzeFileRelationships f files) files
  
  -- Build nodes
  let nodes = Array.map (\file ->
        -- Find relationships where this file is the target (incoming dependencies)
        let incoming = Array.filter (\rel -> rel.file == file) allRelationships
        
        -- Find relationships where this file is the source (outgoing dependencies)
        -- We need to track which file created each relationship
        -- For now, we'll count relationships where this file appears
        -- In a full implementation, we'd track source file in relationship
        let outgoing = Array.filter (\rel ->
              -- Check if relationship indicates this file depends on rel.file
              rel.relationship == Imports || rel.relationship == Uses
            ) allRelationships
        in
          { file: file
          , type_: detectFileType file
          , dependencies: Array.length outgoing
          , dependents: Array.length incoming
          }
      ) files
  
  -- Build edges from relationships
  -- Note: We need to track source file for each relationship
  -- For now, we'll create edges based on relationship type
  let edges = Array.concatMap (\file ->
        -- Find relationships for this file
        let fileRelationships = Array.filter (\rel -> rel.file == file) allRelationships
        in
          Array.map (\rel ->
            { from: file  -- Source file
            , to: rel.file  -- Target file
            , relationship: rel.relationship
            , weight: rel.strength
            }
          ) fileRelationships
      ) files
  
  pure
    { nodes: nodes
    , edges: edges
    }

-- | Detect file type
detectFileType :: String -> FileType
detectFileType filePath =
  if String.contains (String.Pattern "test") filePath ||
     String.contains (String.Pattern "Test") filePath ||
     String.contains (String.Pattern "spec") filePath then
    TestFile
  else if String.contains (String.Pattern "config") filePath ||
          String.contains (String.Pattern ".json") filePath ||
          String.contains (String.Pattern ".dhall") filePath then
    ConfigFile
  else if String.contains (String.Pattern ".md") filePath then
    DocumentationFile
  else
    SourceFile
