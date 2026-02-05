{-|
Module      : Sidepanel.Components.MultiFileContext.ImportAnalyzer
Description : Analyze imports and exports across files
Analyzes import/export relationships between files.
-}
module Sidepanel.Components.MultiFileContext.ImportAnalyzer where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)
import Sidepanel.Components.MultiFileContext.FileRelationshipTypes
  ( ImportAnalysis
  , ImportInfo
  , ImportType(..)
  , ExportInfo
  , SymbolType(..)
  )

-- | Analyze imports for a file
analyzeImports :: String -> String -> Aff ImportAnalysis
analyzeImports filePath content = do
  -- Extract imports based on language
  let language = detectLanguage filePath
  let imports = extractImports language content
  let exports = extractExports language content
  
  -- Resolve import paths to actual files
  let resolvedImports = Array.mapMaybe (resolveImport filePath) imports
  
  -- Find transitive imports
  let transitiveImports = findTransitiveImports resolvedImports
  
  pure
    { file: filePath
    , imports: resolvedImports
    , exports: exports
    , transitiveImports: transitiveImports
    }

-- | Detect language from file extension
detectLanguage :: String -> String
detectLanguage filePath =
  let ext = String.dropWhile (\c -> c /= '.') filePath
  in
    case ext of
      ".purs" -> "purescript"
      ".hs" -> "haskell"
      ".ts" -> "typescript"
      ".tsx" -> "typescript"
      ".js" -> "javascript"
      ".jsx" -> "javascript"
      ".lean" -> "lean4"
      _ -> "unknown"

-- | Extract imports from content
extractImports :: String -> String -> Array ImportInfo
extractImports language content =
  case language of
    "purescript" -> extractPureScriptImports content
    "haskell" -> extractHaskellImports content
    "typescript" -> extractTypeScriptImports content
    "javascript" -> extractJavaScriptImports content
    _ -> []

-- | Extract PureScript imports
extractPureScriptImports :: String -> Array ImportInfo
extractPureScriptImports content =
  let lines = String.split (String.Pattern "\n") content
      importLines = Array.filter (\l -> String.contains (String.Pattern "import ") l) lines
  in
    Array.mapMaybe parsePureScriptImport importLines

-- | Parse single PureScript import
parsePureScriptImport :: String -> Maybe ImportInfo
parsePureScriptImport line =
  if String.contains (String.Pattern "import ") line then
    let parts = String.split (String.Pattern " ") (String.trim line)
        moduleName = case Array.index parts 1 of
          Nothing -> ""
          Just name -> name
        qualified = String.contains (String.Pattern "qualified") line
        hiding = String.contains (String.Pattern "hiding") line
        symbols = extractImportSymbols line
    in
      Just
        { module: moduleName
        , file: ""  -- Will be resolved
        , symbols: symbols
        , importType: if qualified then NamespaceImport else NamedImport
        }
  else
    Nothing

-- | Extract import symbols from line
extractImportSymbols :: String -> Array String
extractImportSymbols line =
  -- Extract symbols from (A, B, C) pattern
  let openParen = String.indexOf (String.Pattern "(") line
      closeParen = String.indexOf (String.Pattern ")") line
  in
    case openParen, closeParen of
      Just start, Just end ->
        let symbolsStr = String.substring start (end + 1) line
            symbols = String.split (String.Pattern ",") symbolsStr
        in
          Array.map String.trim symbols
      _, _ -> []

-- | Extract Haskell imports
extractHaskellImports :: String -> Array ImportInfo
extractHaskellImports content =
  let lines = String.split (String.Pattern "\n") content
      importLines = Array.filter (\l -> String.contains (String.Pattern "import ") l) lines
  in
    Array.mapMaybe parseHaskellImport importLines

-- | Parse single Haskell import
parseHaskellImport :: String -> Maybe ImportInfo
parseHaskellImport line =
  if String.contains (String.Pattern "import ") line then
    let parts = String.split (String.Pattern " ") (String.trim line)
        moduleName = case Array.index parts 1 of
          Nothing -> ""
          Just name -> name
        qualified = String.contains (String.Pattern "qualified") line
        symbols = extractImportSymbols line
    in
      Just
        { module: moduleName
        , file: ""
        , symbols: symbols
        , importType: if qualified then NamespaceImport else NamedImport
        }
  else
    Nothing

-- | Extract TypeScript imports
extractTypeScriptImports :: String -> Array ImportInfo
extractTypeScriptImports content =
  let lines = String.split (String.Pattern "\n") content
      importLines = Array.filter (\l -> String.contains (String.Pattern "import ") l) lines
  in
    Array.mapMaybe parseTypeScriptImport importLines

-- | Parse single TypeScript import
parseTypeScriptImport :: String -> Maybe ImportInfo
parseTypeScriptImport line =
  if String.contains (String.Pattern "import ") line then
    -- Match: import { A, B } from "module"
    -- or: import A from "module"
    -- or: import * as A from "module"
    let fromMatch = String.indexOf (String.Pattern "from") line
        moduleMatch = case fromMatch of
          Nothing -> Nothing
          Just idx -> 
            let afterFrom = String.drop (idx + 4) line
                moduleName = String.trim (String.dropWhile (\c -> c == ' ' || c == '"' || c == '\'') afterFrom)
                moduleName' = String.takeWhile (\c -> c /= '"' && c /= '\'' && c /= ';') moduleName
            in
              Just moduleName'
        
        hasNamespace = String.contains (String.Pattern "* as") line
        hasBraces = String.contains (String.Pattern "{") line
        symbols = if hasBraces then extractImportSymbols line else []
    in
      case moduleMatch of
        Nothing -> Nothing
        Just moduleName ->
          Just
            { module: moduleName
            , file: ""
            , symbols: symbols
            , importType: if hasNamespace then NamespaceImport else if hasBraces then NamedImport else DefaultImport
            }
  else
    Nothing

-- | Extract JavaScript imports (same as TypeScript)
extractJavaScriptImports :: String -> Array ImportInfo
extractJavaScriptImports = extractTypeScriptImports

-- | Extract exports from content
extractExports :: String -> String -> Array ExportInfo
extractExports language content =
  case language of
    "purescript" -> extractPureScriptExports content
    "haskell" -> extractHaskellExports content
    "typescript" -> extractTypeScriptExports content
    _ -> []

-- | Extract PureScript exports
extractPureScriptExports :: String -> Array ExportInfo
extractPureScriptExports content =
  -- PureScript exports are implicit (everything is exported unless private)
  -- Would need AST analysis for accurate extraction
  []

-- | Extract Haskell exports
extractHaskellExports :: String -> Array ExportInfo
extractHaskellExports content =
  -- Look for module X (A, B, C) where pattern
  let moduleLine = Array.find (\l -> String.contains (String.Pattern "module ") l) (String.split (String.Pattern "\n") content)
  in
    case moduleLine of
      Nothing -> []
      Just line ->
        let symbols = extractImportSymbols line
        in
          Array.map (\s ->
            { symbol: s
            , symbolType: FunctionSymbol  -- Would need type inference
            , exportedAs: s
            }
          ) symbols

-- | Extract TypeScript exports
extractTypeScriptExports :: String -> Array ExportInfo
extractTypeScriptExports content =
  let lines = String.split (String.Pattern "\n") content
      exportLines = Array.filter (\l -> String.contains (String.Pattern "export ") l) lines
  in
    Array.mapMaybe parseTypeScriptExport exportLines

-- | Parse TypeScript export
parseTypeScriptExport :: String -> Maybe ExportInfo
parseTypeScriptExport line =
  if String.contains (String.Pattern "export ") line then
    -- Match: export function name
    -- or: export const name
    -- or: export { name }
    let symbols = extractImportSymbols line
    in
      case Array.head symbols of
        Nothing -> Nothing
        Just symbol ->
          Just
            { symbol: symbol
            , symbolType: FunctionSymbol
            , exportedAs: symbol
            }
  else
    Nothing

-- | Resolve import to file path
resolveImport :: String -> ImportInfo -> Maybe ImportInfo
resolveImport currentFile importInfo =
  -- Would resolve module name to actual file path
  -- For now, return as-is
  Just importInfo

-- | Find transitive imports
findTransitiveImports :: Array ImportInfo -> Array String
findTransitiveImports imports =
  -- Would recursively find all files imported by imported files
  -- For now, return empty
  []
