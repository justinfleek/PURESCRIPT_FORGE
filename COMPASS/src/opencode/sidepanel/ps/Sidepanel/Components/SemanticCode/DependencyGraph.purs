{-|
Module      : Sidepanel.Components.SemanticCode.DependencyGraph
Description : Build and visualize dependency graphs
Builds dependency graphs showing imports, exports, and call relationships.
-}
module Sidepanel.Components.SemanticCode.DependencyGraph where

import Prelude

import Data.Array as Array
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)
import Sidepanel.Components.SemanticCode.DependencyGraphTypes
  ( DependencyGraph
  , FileNode
  , DependencyEdge
  , EdgeType(..)
  , FileRelationship(..)
  )

-- | Build dependency graph from file relationships
buildDependencyGraph :: Array { file :: String, imports :: Array String, exports :: Array String } -> DependencyGraph
buildDependencyGraph fileData = do
  let nodes = Array.map (\data -> createFileNode data.file data.imports data.exports) fileData
  let edges = buildEdges fileData
  
  { nodes: nodes
  , edges: edges
  , rootNodes: findRootNodes nodes edges
  }

-- | Create file node
createFileNode :: String -> Array String -> Array String -> FileNode
createFileNode filePath imports exports =
  { id: filePath
  , path: filePath
  , name: extractFileName filePath
  , imports: imports
  , exports: exports
  , type_: detectFileType filePath
  , size: 0  -- Would calculate actual file size
  , complexity: 0.0  -- Would calculate complexity
  }

-- | Extract file name from path
extractFileName :: String -> String
extractFileName path =
  let parts = String.split (String.Pattern "/") path
  in
    fromMaybe path (Array.last parts)

-- | Detect file type
detectFileType :: String -> String
detectFileType path =
  if String.contains (String.Pattern ".purs") path then "purescript"
  else if String.contains (String.Pattern ".hs") path then "haskell"
  else if String.contains (String.Pattern ".lean") path then "lean4"
  else if String.contains (String.Pattern ".ts") path then "typescript"
  else if String.contains (String.Pattern ".js") path then "javascript"
  else "unknown"

-- | Build edges from file data
buildEdges :: Array { file :: String, imports :: Array String, exports :: Array String } -> Array DependencyEdge
buildEdges fileData = do
  Array.concatMap (\data ->
    Array.mapMaybe (\imported ->
      case findFileByModule imported fileData of
        Nothing -> Nothing
        Just targetFile ->
          Just
            { from: data.file
            , to: targetFile
            , type_: ImportEdge
            , strength: 1.0  -- Would calculate based on number of imports
            , label: imported
            }
    ) data.imports
  ) fileData

-- | Find file by module name
findFileByModule :: String -> Array { file :: String, imports :: Array String, exports :: Array String } -> Maybe String
findFileByModule moduleName fileData =
  Array.findMap (\data ->
    if Array.elem moduleName data.exports then
      Just data.file
    else
      Nothing
  ) fileData

-- | Find root nodes (nodes with no incoming edges)
findRootNodes :: Array FileNode -> Array DependencyEdge -> Array FileNode
findRootNodes nodes edges = do
  let nodesWithIncoming = Array.map _.to edges
  Array.filter (\node -> not (Array.elem node.id nodesWithIncoming)) nodes

-- | Get dependencies for a file
getDependencies :: DependencyGraph -> String -> Array FileNode
getDependencies graph fileId = do
  let outgoingEdges = Array.filter (\edge -> edge.from == fileId) graph.edges
  Array.mapMaybe (\edge -> Array.find (\node -> node.id == edge.to) graph.nodes) outgoingEdges

-- | Get dependents for a file (files that depend on this file)
getDependents :: DependencyGraph -> String -> Array FileNode
getDependents graph fileId = do
  let incomingEdges = Array.filter (\edge -> edge.to == fileId) graph.edges
  Array.mapMaybe (\edge -> Array.find (\node -> node.id == edge.from) graph.nodes) incomingEdges

-- | Find transitive dependencies
findTransitiveDependencies :: DependencyGraph -> String -> Array FileNode
findTransitiveDependencies graph fileId = do
  findTransitiveDependenciesHelper graph fileId []

-- | Helper for transitive dependencies
findTransitiveDependenciesHelper :: DependencyGraph -> String -> Array String -> Array FileNode
findTransitiveDependenciesHelper graph fileId visited = do
  if Array.elem fileId visited then
    []
  else
    let directDeps = getDependencies graph fileId
        newVisited = visited <> [fileId]
        transitiveDeps = Array.concatMap (\dep -> findTransitiveDependenciesHelper graph dep.id newVisited) directDeps
    in
      directDeps <> transitiveDeps

-- | Find circular dependencies
findCircularDependencies :: DependencyGraph -> Array (Array String)
findCircularDependencies graph = do
  Array.concatMap (\node -> findCyclesFromNode graph node.id []) graph.nodes

-- | Find cycles starting from a node
findCyclesFromNode :: DependencyGraph -> String -> Array String -> Array (Array String)
findCyclesFromNode graph nodeId path = do
  if Array.elem nodeId path then
    -- Found a cycle
    let cycleStart = fromMaybe 0 (Array.findIndex (\id -> id == nodeId) path)
        cycle = Array.slice cycleStart (Array.length path) path <> [nodeId]
    in
      [cycle]
  else
    let newPath = path <> [nodeId]
        dependencies = getDependencies graph nodeId
        cycles = Array.concatMap (\dep -> findCyclesFromNode graph dep.id newPath) dependencies
    in
      cycles

-- | Calculate dependency depth
calculateDependencyDepth :: DependencyGraph -> String -> Int
calculateDependencyDepth graph fileId = do
  calculateDependencyDepthHelper graph fileId 0 []

-- | Helper for dependency depth
calculateDependencyDepthHelper :: DependencyGraph -> String -> Int -> Array String -> Int
calculateDependencyDepthHelper graph fileId currentDepth visited = do
  if Array.elem fileId visited then
    currentDepth  -- Circular dependency, return current depth
  else
    let dependencies = getDependencies graph fileId
        newVisited = visited <> [fileId]
    in
      if Array.length dependencies == 0 then
        currentDepth
      else
        Array.foldl (\maxDepth dep ->
          let depDepth = calculateDependencyDepthHelper graph dep.id (currentDepth + 1) newVisited
          in
            if depDepth > maxDepth then depDepth else maxDepth
        ) currentDepth dependencies

-- | Get critical path (longest dependency chain)
getCriticalPath :: DependencyGraph -> Array String
getCriticalPath graph = do
  let rootNodes = findRootNodes graph.nodes graph.edges
  Array.foldl (\longestPath root ->
    let path = getLongestPathFromNode graph root.id []
    in
      if Array.length path > Array.length longestPath then path else longestPath
  ) [] rootNodes

-- | Get longest path from a node
getLongestPathFromNode :: DependencyGraph -> String -> Array String -> Array String
getLongestPathFromNode graph nodeId currentPath = do
  if Array.elem nodeId currentPath then
    currentPath  -- Circular dependency, return current path
  else
    let newPath = currentPath <> [nodeId]
        dependencies = getDependencies graph nodeId
    in
      if Array.length dependencies == 0 then
        newPath
      else
        Array.foldl (\longestPath dep ->
          let depPath = getLongestPathFromNode graph dep.id newPath
          in
            if Array.length depPath > Array.length longestPath then depPath else longestPath
        ) newPath dependencies
