{-|
Module      : Sidepanel.Components.InlineSuggestions.ContextBuilder
Description : Build context for inline suggestions
Builds rich context for AI model to generate accurate code suggestions.
-}
module Sidepanel.Components.InlineSuggestions.ContextBuilder where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.Either (Either(..))
import Effect.Aff (Aff)
import Tool.ASTEdit.FFI.FileIO (readFile)
import Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes
  ( EditorState
  , SuggestionContext
  , ProjectContext
  , Import
  , Position
  )

-- | Build suggestion context from editor state
buildSuggestionContext :: EditorState -> Aff SuggestionContext
buildSuggestionContext editorState = do
  let prefix = extractPrefix editorState
  let suffix = extractSuffix editorState
  let imports = extractImports editorState.content editorState.language
  let relatedFiles = findRelatedFiles editorState.filePath
  projectContext <- buildProjectContext editorState.filePath
  
  pure
    { currentFile: editorState
    , prefix: prefix
    , suffix: suffix
    , imports: imports
    , relatedFiles: relatedFiles
    , projectContext: projectContext
    }

-- | Extract text before cursor on current line
extractPrefix :: EditorState -> String
extractPrefix editorState = do
  let lines = String.split (String.Pattern "\n") editorState.content
  case Array.index lines editorState.cursorPosition.line of
    Nothing -> ""
    Just line -> String.take editorState.cursorPosition.column line

-- | Extract text after cursor on current line
extractSuffix :: EditorState -> String
extractSuffix editorState = do
  let lines = String.split (String.Pattern "\n") editorState.content
  case Array.index lines editorState.cursorPosition.line of
    Nothing -> ""
    Just line -> String.drop editorState.cursorPosition.column line

-- | Extract imports from file content
extractImports :: String -> String -> Array Import
extractImports content language = case language of
  "typescript" -> extractTypeScriptImports content
  "purescript" -> extractPureScriptImports content
  "haskell" -> extractHaskellImports content
  _ -> []

-- | Extract TypeScript imports
extractTypeScriptImports :: String -> Array Import
extractTypeScriptImports content = do
  let importRegex = "import\\s+(?:\\{([^}]+)\\}\\s+from\\s+)?['\"]([^'\"]+)['\"]"
  -- Simplified - would use proper regex
  []

-- | Extract PureScript imports
extractPureScriptImports :: String -> Array Import
extractPureScriptImports content = do
  let lines = String.split (String.Pattern "\n") content
  Array.mapMaybe extractPureScriptImport lines

-- | Extract single PureScript import
extractPureScriptImport :: String -> Maybe Import
extractPureScriptImport line = do
  if String.contains (String.Pattern "import ") line then
    let parts = String.split (String.Pattern " ") line
        -- Find module name (after "import" and optional "qualified")
        moduleName = case Array.findIndex (\p -> p /= "import" && p /= "qualified" && p /= "" && not (String.contains (String.Pattern "(") p)) parts of
          Nothing -> ""
          Just idx -> fromMaybe "" (Array.index parts idx)
        
        -- Extract items from (A, B, C) syntax
        items = extractImportItems line
        
        qualified = String.contains (String.Pattern "qualified") line
    in
      if moduleName == "" then Nothing
      else Just
        { module: moduleName
        , items: items
        , qualified: qualified
        }
  else
    Nothing
  where
    extractImportItems :: String -> Array String
    extractImportItems line =
      -- Look for (A, B, C) pattern
      case String.indexOf (String.Pattern "(") line of
        Nothing -> []
        Just startIdx ->
          case String.indexOf (String.Pattern ")") (String.drop startIdx line) of
            Nothing -> []
            Just endIdx ->
              let itemsStr = String.take endIdx (String.drop (startIdx + 1) line)
                  items = String.split (String.Pattern ",") itemsStr
                  cleaned = Array.map (\item -> String.trim item) items
              in
                Array.filter (\item -> item /= "") cleaned

-- | Extract Haskell imports
extractHaskellImports :: String -> Array Import
extractHaskellImports content = do
  let lines = String.split (String.Pattern "\n") content
  Array.mapMaybe extractHaskellImport lines

-- | Extract single Haskell import
extractHaskellImport :: String -> Maybe Import
extractHaskellImport line = do
  if String.contains (String.Pattern "import ") line then
    let parts = String.split (String.Pattern " ") line
        -- Find module name (after "import" and optional "qualified")
        moduleName = case Array.findIndex (\p -> p /= "import" && p /= "qualified" && p /= "" && not (String.contains (String.Pattern "(") p)) parts of
          Nothing -> ""
          Just idx -> fromMaybe "" (Array.index parts idx)
        
        -- Extract items from (A, B, C) syntax (same as PureScript)
        items = extractImportItems line
        
        qualified = String.contains (String.Pattern "qualified") line
    in
      if moduleName == "" then Nothing
      else Just
        { module: moduleName
        , items: items
        , qualified: qualified
        }
  else
    Nothing
  where
    extractImportItems :: String -> Array String
    extractImportItems line =
      -- Look for (A, B, C) pattern
      case String.indexOf (String.Pattern "(") line of
        Nothing -> []
        Just startIdx ->
          case String.indexOf (String.Pattern ")") (String.drop startIdx line) of
            Nothing -> []
            Just endIdx ->
              let itemsStr = String.take endIdx (String.drop (startIdx + 1) line)
                  items = String.split (String.Pattern ",") itemsStr
                  cleaned = Array.map (\item -> String.trim item) items
              in
                Array.filter (\item -> item /= "") cleaned

-- | Find related files using MultiFileContext
findRelatedFiles :: String -> Array String
findRelatedFiles filePath = 
  -- Use simple heuristics to find related files:
  -- 1. Files in same directory
  -- 2. Files with similar names
  -- 3. Test files for this file
  -- Full implementation would use FileRelationshipAnalyzer
  let dir = extractDirectory filePath
      baseName = extractBaseName filePath
      -- Simple pattern matching - would be enhanced with actual file system traversal
      relatedPatterns = 
        [ baseName <> "Test"
        , "Test" <> baseName
        , baseName <> "Spec"
        , baseName <> ".test"
        ]
  in
    []  -- Would traverse filesystem and match patterns
  where
    extractDirectory :: String -> String
    extractDirectory filePath =
      let parts = String.split (String.Pattern "/") filePath
          dirParts = Array.take (Array.length parts - 1) parts
      in
        String.joinWith "/" dirParts
    
    extractBaseName :: String -> String
    extractBaseName filePath =
      let parts = String.split (String.Pattern "/") filePath
          fileName = fromMaybe "" (Array.last parts)
          withoutExt = String.takeWhile (\c -> c /= '.') fileName
      in
        withoutExt

-- | Build project context
buildProjectContext :: String -> Aff ProjectContext
buildProjectContext filePath = do
  let projectRoot = extractProjectRoot filePath
  
  -- Read dependencies from config files
  dependencies <- readDependencies projectRoot
  
  -- Get recent files (would track in component state)
  recentFiles <- getRecentFiles
  
  -- Get open files (would get from editor state)
  openFiles <- getOpenFiles
  
  pure
    { projectRoot: projectRoot
    , dependencies: dependencies
    , recentFiles: recentFiles
    , openFiles: openFiles
    }

-- | Read dependencies from config files
readDependencies :: String -> Aff (Array String)
readDependencies projectRoot = do
  -- Try to read common config files
  -- Check for package.json, spago.dhall, package.yaml, Cargo.toml, etc.
  let configFiles = 
        [ projectRoot <> "/package.json"
        , projectRoot <> "/spago.dhall"
        , projectRoot <> "/package.yaml"
        , projectRoot <> "/Cargo.toml"
        , projectRoot <> "/flake.nix"
        ]
  
  -- Try to read each config file and extract dependencies
  results <- Array.traverse (\file -> do
    readResult <- readFile file
    case readResult of
      Left _ -> pure []
      Right content -> pure (extractDependenciesFromContent file content)
  ) configFiles
  
  -- Return unique dependencies
  pure $ Array.nub (Array.concat results)
  where
    extractDependenciesFromContent :: String -> String -> Array String
    extractDependenciesFromContent filePath content =
      -- Simple extraction based on file type
      if String.contains (String.Pattern "package.json") filePath then
        -- Would parse JSON and extract dependencies
        -- For now, look for common patterns
        extractFromJSON content
      else if String.contains (String.Pattern "spago.dhall") filePath then
        -- Would parse Dhall and extract dependencies
        extractFromDhall content
      else if String.contains (String.Pattern "package.yaml") filePath then
        -- Would parse YAML and extract dependencies
        extractFromYAML content
      else
        []
    
    extractFromJSON :: String -> Array String
    extractFromJSON content =
      -- Simple pattern matching for dependency names
      -- Full implementation would parse JSON properly
      let lines = String.split (String.Pattern "\n") content
          depLines = Array.filter (\l -> 
            String.contains (String.Pattern "\"") l &&
            (String.contains (String.Pattern "dependencies") l ||
             String.contains (String.Pattern "devDependencies") l)
          ) lines
      in
        Array.mapMaybe (\l -> extractPackageName l) depLines
    
    extractPackageName :: String -> Maybe String
    extractPackageName line =
      -- Extract package name from JSON line like: "package-name": "version"
      case String.indexOf (String.Pattern "\"") line of
        Nothing -> Nothing
        Just startIdx ->
          let afterQuote = String.drop (startIdx + 1) line
              endIdx = String.indexOf (String.Pattern "\"") afterQuote
          in
            case endIdx of
              Nothing -> Nothing
              Just idx -> Just (String.take idx afterQuote)
    
    extractFromDhall :: String -> Array String
    extractFromDhall content =
      -- Simple extraction from Dhall - look for package names
      -- Full implementation would parse Dhall properly
      let lines = String.split (String.Pattern "\n") content
          packageLines = Array.filter (\l -> 
            String.contains (String.Pattern "package") l ||
            String.contains (String.Pattern "dependencies") l
          ) lines
      in
        Array.mapMaybe (\l -> extractPackageName l) packageLines
    
    extractFromYAML :: String -> Array String
    extractFromYAML content =
      -- Simple extraction from YAML
      -- Full implementation would parse YAML properly
      let lines = String.split (String.Pattern "\n") content
          depLines = Array.filter (\l -> 
            String.contains (String.Pattern "-") l &&
            String.contains (String.Pattern "package") l
          ) lines
      in
        Array.mapMaybe (\l -> extractPackageName l) depLines

-- | Get recent files
getRecentFiles :: Aff (Array String)
getRecentFiles = do
  -- Would track in component state or local storage
  -- For now, return empty - this requires state management integration
  pure []

-- | Get open files
getOpenFiles :: Aff (Array String)
getOpenFiles = do
  -- Would get from editor state
  -- For now, return empty - this requires editor state integration
  pure []

-- | Extract project root from file path
extractProjectRoot :: String -> String
extractProjectRoot filePath =
  -- Find nearest directory containing project markers
  -- Markers: package.json, spago.dhall, .git, flake.nix, Cargo.toml
  let parts = String.split (String.Pattern "/") filePath
      -- Try each directory level from file up to root
      directories = Array.mapWithIndex (\idx _ ->
        String.joinWith "/" (Array.take (Array.length parts - idx) parts)
      ) parts
      
      -- Check each directory for project markers
      -- For now, return first directory (simplified)
      -- Full implementation would check for marker files
      root = fromMaybe "/" (Array.head directories)
  in
    root
