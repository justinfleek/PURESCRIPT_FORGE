{-|
Module      : Sidepanel.Components.MultiFileContext.FileRelationshipAnalyzer
Description : Analyze relationships between files
Analyzes relationships between files: imports, exports, usage, tests, etc.
-}
module Sidepanel.Components.MultiFileContext.FileRelationshipAnalyzer where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.Either (Either(..))
import Effect.Aff (Aff)
import Tool.ASTEdit.FFI.FileIO (readFile)
import Sidepanel.Components.MultiFileContext.FileRelationshipTypes
  ( FileRelationship
  , RelationshipType(..)
  , Evidence(..)
  , EvidenceType(..)
  , Location
  )
import Sidepanel.Components.MultiFileContext.ImportAnalyzer (analyzeImports)

-- | Analyze file relationships
analyzeFileRelationships :: String -> Array String -> Aff (Array FileRelationship)
analyzeFileRelationships filePath allFiles = do
  -- Read file content
  readResult <- readFile filePath
  let content = case readResult of
        Left _ -> ""  -- If read fails, use empty string
        Right c -> c
  
  importAnalysis <- analyzeImports filePath content
  
  -- Find related files based on imports
  let importRelations = Array.mapMaybe (\imp -> 
        findFileByModule imp.module allFiles >>= \relatedFile ->
        Just
          { file: relatedFile
          , relationship: Imports
          , strength: calculateStrength imp.symbols
          , evidence:
              [ { type_: ImportStatement
                , location: { file: filePath, line: 0, column: 0 }
                , description: "Imports " <> String.joinWith ", " imp.symbols <> " from " <> imp.module
                }
              ]
          }
      ) importAnalysis.imports
  
  -- Find files that import this file
  let exportRelations = findFilesImportingThis filePath allFiles
  
  -- Find test files
  let testRelations = findTestFiles filePath allFiles
  
  -- Find config files
  let configRelations = findConfigFiles filePath allFiles
  
  pure (importRelations <> exportRelations <> testRelations <> configRelations)

-- | Find file by module name
findFileByModule :: String -> Array String -> Maybe String
findFileByModule moduleName files =
  -- Would resolve module name to file path
  -- For now, try simple matching
  Array.find (\f -> String.contains (String.Pattern moduleName) f) files

-- | Calculate relationship strength
calculateStrength :: Array String -> Number
calculateStrength symbols =
  -- More symbols = stronger relationship
  let count = Array.length symbols
  in
    if count > 10 then 1.0
    else if count > 5 then 0.8
    else if count > 2 then 0.6
    else if count > 0 then 0.4
    else 0.2

-- | Find files that import this file
findFilesImportingThis :: String -> Array String -> Array FileRelationship
findFilesImportingThis filePath allFiles =
  -- Extract module name from file path
  -- For PureScript: src/Module/Path.purs -> Module.Path
  -- For other languages: similar pattern matching
  let moduleName = extractModuleNameFromPath filePath
      baseName = extractBaseName filePath
      
      -- Find files that might import this module
      -- Check if file path or content contains module name or base name
      potentialImporters = Array.filter (\f -> 
        f /= filePath &&  -- Don't include self
        (String.contains (String.Pattern moduleName) f ||
         String.contains (String.Pattern baseName) f)
      ) allFiles
      
      -- Build relationships (simplified - would need actual import analysis)
      relationships = Array.map (\f ->
        { file: f
        , relationship: Exports  -- This file exports symbols used by f
        , strength: 0.6  -- Medium strength without full analysis
        , evidence:
            [ { type_: ImportStatement
              , location: { file: f, line: 0, column: 0 }
              , description: "Potentially imports from " <> filePath
              }
            ]
        }
      ) potentialImporters
  in
    relationships

-- | Extract module name from file path
extractModuleNameFromPath :: String -> String
extractModuleNameFromPath filePath =
  -- Remove common prefixes and extensions
  let withoutExt = String.dropSuffix (String.Pattern ".purs") filePath
      withoutExt' = String.dropSuffix (String.Pattern ".hs") withoutExt
      withoutExt'' = String.dropSuffix (String.Pattern ".ts") withoutExt'
      withoutExt''' = String.dropSuffix (String.Pattern ".tsx") withoutExt''
      
      -- Remove common directory prefixes
      withoutSrc = String.replace (String.Pattern "src/") "" withoutExt'''
      withoutLib = String.replace (String.Pattern "lib/") "" withoutSrc
      
      -- Convert path separators to dots (module notation)
      moduleName = String.replaceAll (String.Pattern "/") (String.Replacement ".") withoutLib
  in
    moduleName

-- | Find test files for a file
findTestFiles :: String -> Array String -> Array FileRelationship
findTestFiles filePath allFiles =
  let baseName = extractBaseName filePath
      testPatterns = ["Test" <> baseName, baseName <> "Test", "test/" <> baseName]
      testFiles = Array.filter (\f -> Array.any (\p -> String.contains (String.Pattern p) f) testPatterns) allFiles
  in
    Array.map (\f ->
      { file: f
      , relationship: Tests
      , strength: 0.9
      , evidence:
          [ { type_: TestFile
            , location: { file: f, line: 0, column: 0 }
            , description: "Test file for " <> filePath
            }
          ]
      }
    ) testFiles

-- | Find config files for a file
findConfigFiles :: String -> Array String -> Array FileRelationship
findConfigFiles filePath allFiles =
  let dir = extractDirectory filePath
      configFiles = Array.filter (\f -> 
        String.contains (String.Pattern dir) f &&
        (String.contains (String.Pattern "config") f || 
         String.contains (String.Pattern "package.json") f ||
         String.contains (String.Pattern "spago.dhall") f)
      ) allFiles
  in
    Array.map (\f ->
      { file: f
      , relationship: Config
      , strength: 0.7
      , evidence:
          [ { type_: ConfigFile
            , location: { file: f, line: 0, column: 0 }
            , description: "Configuration file for " <> filePath
            }
          ]
      }
    ) configFiles

-- | Extract base name from file path
extractBaseName :: String -> String
extractBaseName filePath =
  let parts = String.split (String.Pattern "/") filePath
      fileName = fromMaybe "" (Array.last parts)
      withoutExt = String.takeWhile (\c -> c /= '.') fileName
  in
    withoutExt

-- | Extract directory from file path
extractDirectory :: String -> String
extractDirectory filePath =
  let parts = String.split (String.Pattern "/") filePath
      dirParts = Array.take (Array.length parts - 1) parts
  in
    String.joinWith "/" dirParts
