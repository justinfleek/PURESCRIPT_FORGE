{-|
Module      : Sidepanel.Components.SemanticCode.SemanticIndex
Description : Semantic code index for cross-file understanding
Builds and maintains semantic index of codebase for fast symbol lookup.
-}
module Sidepanel.Components.SemanticCode.SemanticIndex where

import Prelude

import Data.Array as Array
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Sidepanel.Components.SemanticCode.LSPClient
  ( SymbolInfo
  , SymbolKind
  , Location
  )

-- | Semantic code index
type SemanticIndex =
  { symbols :: Map.Map SymbolId SymbolInfo
  , files :: Map.Map FilePath (Array SymbolId)
  , references :: Map.Map SymbolId (Array Location)
  , dependencies :: Map.Map FilePath (Array FilePath)
  }

-- | Symbol ID (unique identifier)
type SymbolId = String

-- | File path
type FilePath = String

-- | Build semantic index from LSP
buildSemanticIndex :: Array FilePath -> Aff SemanticIndex
buildSemanticIndex filePaths = do
  -- This would:
  -- 1. Connect to LSP servers for each language
  -- 2. Get document symbols for each file
  -- 3. Build cross-reference map
  -- 4. Build dependency graph
  
  pure
    { symbols: Map.empty
    , files: Map.empty
    , references: Map.empty
    , dependencies: Map.empty
    }

-- | Find symbol by name
findSymbol :: SemanticIndex -> String -> Maybe SymbolInfo
findSymbol index name = do
  -- Search symbols map
  Array.find (\sym -> sym.name == name) (Map.values index.symbols)

-- | Find all references to symbol
findSymbolReferences :: SemanticIndex -> SymbolId -> Array Location
findSymbolReferences index symbolId = do
  fromMaybe [] (Map.lookup symbolId index.references)

-- | Get symbols in file
getFileSymbols :: SemanticIndex -> FilePath -> Array SymbolInfo
getFileSymbols index filePath = do
  case Map.lookup filePath index.files of
    Nothing -> []
    Just symbolIds -> do
      Array.mapMaybe (\id -> Map.lookup id index.symbols) symbolIds

-- | Get file dependencies
getFileDependencies :: SemanticIndex -> FilePath -> Array FilePath
getFileDependencies index filePath = do
  fromMaybe [] (Map.lookup filePath index.dependencies)

-- | Update index when file changes
updateIndexForFile :: SemanticIndex -> FilePath -> Aff SemanticIndex
updateIndexForFile index filePath = do
  -- This would:
  -- 1. Get new symbols from LSP
  -- 2. Remove old symbols for this file
  -- 3. Add new symbols
  -- 4. Update references
  
  pure index

-- | Import fromMaybe
import Data.Maybe (fromMaybe)
