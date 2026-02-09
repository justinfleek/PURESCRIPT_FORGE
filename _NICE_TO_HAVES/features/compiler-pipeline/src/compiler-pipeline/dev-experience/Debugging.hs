{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
-- Phase 7: Debugging Support
module Debugging where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Aeson as JSON
import Parser (PSModule(..), PSDeclaration(..), PSExpression(..), PSValueDeclaration(..))
import Cpp23Generator (generateCpp23Header, generateCpp23Impl)
import TypeChecker (typeCheckModule)

-- | Source map entry
data SourceMapEntry = SourceMapEntry
  { sourceMapGeneratedLine :: Int
  , sourceMapGeneratedColumn :: Int
  , sourceMapSourceLine :: Int
  , sourceMapSourceColumn :: Int
  , sourceMapSourceFile :: T.Text
  , sourceMapName :: Maybe T.Text
  }

-- | Source map
data SourceMap = SourceMap
  { sourceMapVersion :: Int
  , sourceMapFile :: T.Text
  , sourceMapSources :: [T.Text]
  , sourceMapMappings :: [SourceMapEntry]
  }

-- | Generate source map for C++23 → PureScript mapping
generateSourceMap :: PSModule -> T.Text -> T.Text -> SourceMap
generateSourceMap module' sourceFile generatedCode =
  let sourceLines = T.lines sourceFile
      generatedLines = T.lines generatedCode
      mappings = generateMappings module' sourceLines generatedLines sourceFile
  in SourceMap
    { sourceMapVersion = 3
    , sourceMapFile = T.replace ".purs" ".cpp" sourceFile
    , sourceMapSources = [sourceFile]
    , sourceMapMappings = mappings
    }

-- | Generate mappings between source and generated code
generateMappings :: PSModule -> [T.Text] -> [T.Text] -> T.Text -> [SourceMapEntry]
generateMappings module' sourceLines generatedLines sourceFile =
  let declMappings = concatMap (mapDeclarationToGenerated module' sourceLines generatedLines sourceFile) (moduleDeclarations module')
  in declMappings

-- | Map declaration to generated code locations
mapDeclarationToGenerated :: PSModule -> [T.Text] -> [T.Text] -> T.Text -> PSDeclaration -> [SourceMapEntry]
mapDeclarationToGenerated module' sourceLines generatedLines sourceFile (PSValueDecl decl) =
  let sourceLine = findSourceLine (valueName decl) sourceLines
      generatedLine = findGeneratedLine (valueName decl) generatedLines
  in if sourceLine >= 0 && generatedLine >= 0
    then [SourceMapEntry generatedLine 0 sourceLine 0 sourceFile (Just (valueName decl))]
    else []
mapDeclarationToGenerated _ _ _ _ _ = []

-- | Find source line for declaration
findSourceLine :: T.Text -> [T.Text] -> Int
findSourceLine name lines =
  case findIndex (T.isInfixOf name) lines of
    Just idx -> idx
    Nothing -> -1

-- | Find generated line for declaration
findGeneratedLine :: T.Text -> [T.Text] -> Int
findGeneratedLine name lines =
  case findIndex (T.isInfixOf name) lines of
    Just idx -> idx
    Nothing -> -1

-- | Format source map in JSON format
formatSourceMap :: SourceMap -> T.Text
formatSourceMap SourceMap{..} =
  let mappings = formatMappings sourceMapMappings
      json = JSON.object
        [ ("version", JSON.toJSON sourceMapVersion)
        , ("file", JSON.toJSON sourceMapFile)
        , ("sources", JSON.toJSON sourceMapSources)
        , ("mappings", JSON.toJSON mappings)
        ]
  in T.pack (JSON.encode json)

-- | Format mappings in VLQ format (simplified)
formatMappings :: [SourceMapEntry] -> T.Text
formatMappings entries =
  T.unlines $ map formatMapping entries

formatMapping :: SourceMapEntry -> T.Text
formatMapping SourceMapEntry{..} =
  T.pack (show sourceMapGeneratedLine) <> ":" <>
  T.pack (show sourceMapGeneratedColumn) <> "->" <>
  T.pack (show sourceMapSourceLine) <> ":" <>
  T.pack (show sourceMapSourceColumn) <>
  maybe "" (":" <>) sourceMapName

-- | Breakpoint information
data Breakpoint = Breakpoint
  { breakpointId :: Int
  , breakpointSourceFile :: T.Text
  , breakpointLine :: Int
  , breakpointColumn :: Maybe Int
  , breakpointCondition :: Maybe T.Text
  , breakpointHitCount :: Maybe Int
  , breakpointEnabled :: Bool
  }

-- | Debug session
data DebugSession = DebugSession
  { debugSessionId :: T.Text
  , debugSessionBreakpoints :: Map.Map Int Breakpoint
  , debugSessionVariables :: Map.Map T.Text T.Text
  , debugSessionCallStack :: [CallFrame]
  , debugSessionState :: DebugState
  }

data CallFrame = CallFrame
  { callFrameName :: T.Text
  , callFrameFile :: T.Text
  , callFrameLine :: Int
  , callFrameColumn :: Int
  , callFrameVariables :: Map.Map T.Text T.Text
  }

data DebugState = Running | Paused | Stopped | Stepping

-- | Initialize debug session
initDebugSession :: T.Text -> IO DebugSession
initDebugSession sessionId = do
  return DebugSession
    { debugSessionId = sessionId
    , debugSessionBreakpoints = Map.empty
    , debugSessionVariables = Map.empty
    , debugSessionCallStack = []
    , debugSessionState = Stopped
    }

-- | Set breakpoint
setBreakpoint :: DebugSession -> Breakpoint -> DebugSession
setBreakpoint session bp =
  session { debugSessionBreakpoints = Map.insert (breakpointId bp) bp (debugSessionBreakpoints session) }

-- | Remove breakpoint
removeBreakpoint :: DebugSession -> Int -> DebugSession
removeBreakpoint session bpId =
  session { debugSessionBreakpoints = Map.delete bpId (debugSessionBreakpoints session) }

-- | Check if breakpoint should hit
checkBreakpoint :: DebugSession -> T.Text -> Int -> Bool
checkBreakpoint session file line =
  any (\bp -> breakpointSourceFile bp == file && 
              breakpointLine bp == line && 
              breakpointEnabled bp) (Map.elems (debugSessionBreakpoints session))

-- | Get variable value
getVariableValue :: DebugSession -> T.Text -> Maybe T.Text
getVariableValue session name = Map.lookup name (debugSessionVariables session)

-- | Set variable value
setVariableValue :: DebugSession -> T.Text -> T.Text -> DebugSession
setVariableValue session name value =
  session { debugSessionVariables = Map.insert name value (debugSessionVariables session) }

-- | Add call frame
addCallFrame :: DebugSession -> CallFrame -> DebugSession
addCallFrame session frame =
  session { debugSessionCallStack = frame : debugSessionCallStack session }

-- | Pop call frame
popCallFrame :: DebugSession -> DebugSession
popCallFrame session =
  case debugSessionCallStack session of
    [] -> session
    (_:rest) -> session { debugSessionCallStack = rest }

-- | Generate debug symbols
generateDebugSymbols :: PSModule -> T.Text
generateDebugSymbols module' =
  let symbols = map generateSymbol (moduleDeclarations module')
  in T.unlines symbols

-- | Generate symbol for declaration
generateSymbol :: PSDeclaration -> T.Text
generateSymbol (PSValueDecl decl) =
  "SYMBOL: " <> valueName decl <> " -> " <> T.pack (show (getDeclarationLocation decl))
generateSymbol _ = ""

-- | Get declaration location (simplified)
getDeclarationLocation :: PSValueDeclaration -> (Int, Int)
getDeclarationLocation _ = (0, 0)  -- Would be populated from actual source position

-- | Generate debug info for C++ code
generateDebugInfo :: PSModule -> T.Text
generateDebugInfo module' = T.unlines
  [ "// Debug information"
  , "// Generated from PureScript module: " <> moduleName module'
  , ""
  , "#ifdef DEBUG"
  , "#include <iostream>"
  , "#include <string>"
  , ""
  , "namespace debug {"
  , ""
  , "void printVariable(const std::string& name, const auto& value) {"
  , "  std::cout << \"[DEBUG] \" << name << \" = \" << value << std::endl;"
  , "}"
  , ""
  , "void printCallStack() {"
  , "  std::cout << \"[DEBUG] Call stack:\" << std::endl;"
  , "  // Call stack would be populated at runtime"
  , "}"
  , ""
  , "void breakpoint(const std::string& file, int line) {"
  , "  std::cout << \"[DEBUG] Breakpoint hit: \" << file << \":\" << line << std::endl;"
  , "  // In actual implementation, this would pause execution"
  , "}"
  , ""
  , "} // namespace debug"
  , ""
  , "#endif // DEBUG"
  ]

-- | Instrument code with debug statements
instrumentWithDebug :: PSModule -> PSModule
instrumentWithDebug module'@PSModule{..} =
  let instrumented = map instrumentDeclaration moduleDeclarations
  in module' { moduleDeclarations = instrumented }

-- | Instrument declaration with debug statements
instrumentDeclaration :: PSDeclaration -> PSDeclaration
instrumentDeclaration (PSValueDecl decl) =
  PSValueDecl decl { valueExpression = instrumentExpression (valueExpression decl) }
instrumentDeclaration decl = decl

-- | Instrument expression with debug statements
instrumentExpression :: PSExpression -> PSExpression
instrumentExpression expr@(PSVar v) = 
  -- Add debug print before variable access (simplified - would need proper debug infrastructure)
  expr
instrumentExpression expr@(PSApp f x) =
  -- Add debug print before function call (simplified - would need proper debug infrastructure)
  expr
instrumentExpression expr = expr

-- Helper functions
findIndex :: (a -> Bool) -> [a] -> Maybe Int
findIndex p = go 0
  where
    go _ [] = Nothing
    go n (x:xs) | p x = Just n
                | otherwise = go (n+1) xs

instance JSON.ToJSON SourceMapEntry where
  toJSON SourceMapEntry{..} = JSON.object
    [ ("generatedLine", JSON.toJSON sourceMapGeneratedLine)
    , ("generatedColumn", JSON.toJSON sourceMapGeneratedColumn)
    , ("sourceLine", JSON.toJSON sourceMapSourceLine)
    , ("sourceColumn", JSON.toJSON sourceMapSourceColumn)
    , ("sourceFile", JSON.toJSON sourceMapSourceFile)
    , ("name", JSON.toJSON sourceMapName)
    ]

instance JSON.ToJSON Breakpoint where
  toJSON Breakpoint{..} = JSON.object
    [ ("id", JSON.toJSON breakpointId)
    , ("sourceFile", JSON.toJSON breakpointSourceFile)
    , ("line", JSON.toJSON breakpointLine)
    , ("column", JSON.toJSON breakpointColumn)
    , ("condition", JSON.toJSON breakpointCondition)
    , ("hitCount", JSON.toJSON breakpointHitCount)
    , ("enabled", JSON.toJSON breakpointEnabled)
    ]

instance JSON.ToJSON CallFrame where
  toJSON CallFrame{..} = JSON.object
    [ ("name", JSON.toJSON callFrameName)
    , ("file", JSON.toJSON callFrameFile)
    , ("line", JSON.toJSON callFrameLine)
    , ("column", JSON.toJSON callFrameColumn)
    , ("variables", JSON.toJSON callFrameVariables)
    ]
