{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
-- Phase 7: Language Server Protocol
module LSP where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Aeson as JSON
import qualified Data.Aeson.Types as JSON
import qualified Network.URI as URI
import qualified System.FilePath as FP
import qualified System.Directory as Dir
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.List as L
import Text.Megaparsec (SourcePos(..), unPos)
import Parser (PSModule(..), PSDeclaration(..), PSValueDeclaration(..),
               PSDataDeclaration(..), PSTypeDeclaration(..), PSClassDeclaration(..),
               PSExpression(..), parseModule)
import TypeChecker (typeCheckModule, TypeContext(..), inferType)
import Cpp23Generator (generateCpp23Header, generateCpp23Impl)

-- | LSP Server state
data LSPServer = LSPServer
  { lspDocuments :: Map.Map T.Text DocumentState
  , lspWorkspaceRoot :: FilePath
  }

-- | Document state cache
data DocumentState = DocumentState
  { docContent :: T.Text
  , docAST :: Either T.Text PSModule
  , docVersion :: Int
  }

-- | Initialize LSP server
initLSPServer :: FilePath -> IO LSPServer
initLSPServer workspaceRoot = do
  return LSPServer
    { lspDocuments = Map.empty
    , lspWorkspaceRoot = workspaceRoot
    }

-- | Handle LSP request
handleLSPRequest :: LSPServer -> JSON.Value -> IO (JSON.Value, LSPServer)
handleLSPRequest server request = do
  case JSON.lookup "method" request of
    Just (JSON.String "textDocument/completion") -> handleCompletion server request
    Just (JSON.String "textDocument/hover") -> handleHover server request
    Just (JSON.String "textDocument/definition") -> handleDefinition server request
    Just (JSON.String "textDocument/references") -> handleReferences server request
    Just (JSON.String "textDocument/diagnostic") -> handleDiagnostic server request
    Just (JSON.String "textDocument/didOpen") -> handleDidOpen server request
    Just (JSON.String "textDocument/didChange") -> handleDidChange server request
    Just (JSON.String "textDocument/didClose") -> handleDidClose server request
    _ -> return (JSON.object [("error", JSON.String "Unknown method")], server)

-- | Handle document open
handleDidOpen :: LSPServer -> JSON.Value -> IO (JSON.Value, LSPServer)
handleDidOpen server request = do
  case extractTextDocument request of
    Just (uri, content, version) -> do
      let ast = case parseModule content of
            Left err -> Left $ T.pack (show err)
            Right m -> Right m
      let docState = DocumentState content ast version
      let updated = Map.insert uri docState (lspDocuments server)
      return (JSON.Null, server { lspDocuments = updated })
    Nothing -> return (JSON.Null, server)

-- | Handle document change
handleDidChange :: LSPServer -> JSON.Value -> IO (JSON.Value, LSPServer)
handleDidChange server request = do
  case extractTextDocument request of
    Just (uri, content, version) -> do
      let ast = case parseModule content of
            Left err -> Left $ T.pack (show err)
            Right m -> Right m
      let docState = DocumentState content ast version
      let updated = Map.insert uri docState (lspDocuments server)
      return (JSON.Null, server { lspDocuments = updated })
    Nothing -> return (JSON.Null, server)

-- | Handle document close
handleDidClose :: LSPServer -> JSON.Value -> IO (JSON.Value, LSPServer)
handleDidClose server request = do
  case extractURI request of
    Just uri -> do
      let updated = Map.delete uri (lspDocuments server)
      return (JSON.Null, server { lspDocuments = updated })
    Nothing -> return (JSON.Null, server)

-- | Handle completion request
handleCompletion :: LSPServer -> JSON.Value -> IO (JSON.Value, LSPServer)
handleCompletion server request = do
  case extractTextDocumentPosition request of
    Just (uri, pos) -> do
      case Map.lookup uri (lspDocuments server) of
        Just docState -> do
          case docAST docState of
            Right ast -> do
              let completions = getCompletionsAtPosition ast pos (docContent docState)
              let response = JSON.object
                    [ ("items", JSON.toJSON completions)
                    ]
              return (response, server)
            Left _ -> return (JSON.object [("items", JSON.Array [])], server)
        Nothing -> return (JSON.object [("items", JSON.Array [])], server)
    Nothing -> return (JSON.object [("items", JSON.Array [])], server)

-- | Handle hover request
handleHover :: LSPServer -> JSON.Value -> IO (JSON.Value, LSPServer)
handleHover server request = do
  case extractTextDocumentPosition request of
    Just (uri, pos) -> do
      case Map.lookup uri (lspDocuments server) of
        Just docState -> do
          case docAST docState of
            Right ast -> do
              let hoverInfo = getHoverInfo ast pos (docContent docState)
              let response = JSON.object
                    [ ("contents", JSON.toJSON hoverInfo)
                    ]
              return (response, server)
            Left _ -> return (JSON.Null, server)
        Nothing -> return (JSON.Null, server)
    Nothing -> return (JSON.Null, server)

-- | Handle definition request
handleDefinition :: LSPServer -> JSON.Value -> IO (JSON.Value, LSPServer)
handleDefinition server request = do
  case extractTextDocumentPosition request of
    Just (uri, pos) -> do
      case Map.lookup uri (lspDocuments server) of
        Just docState -> do
          case docAST docState of
            Right ast -> do
              let definition = findDefinition ast pos uri (docContent docState)
              let response = JSON.object
                    [ ("location", JSON.toJSON definition)
                    ]
              return (response, server)
            Left _ -> return (JSON.Null, server)
        Nothing -> return (JSON.Null, server)
    Nothing -> return (JSON.Null, server)

-- | Handle references request
handleReferences :: LSPServer -> JSON.Value -> IO (JSON.Value, LSPServer)
handleReferences server request = do
  case extractTextDocumentPosition request of
    Just (uri, pos) -> do
      let allRefs = Map.foldlWithKey (\acc docUri docState ->
            case docAST docState of
              Right ast -> acc ++ findReferences ast pos docUri (docContent docState)
              Left _ -> acc
            ) [] (lspDocuments server)
      let response = JSON.object
            [ ("locations", JSON.toJSON allRefs)
            ]
      return (response, server)
    Nothing -> return (JSON.object [("locations", JSON.Array [])], server)

-- | Handle diagnostic request
handleDiagnostic :: LSPServer -> JSON.Value -> IO (JSON.Value, LSPServer)
handleDiagnostic server request = do
  case extractURI request of
    Just uri -> do
      case Map.lookup uri (lspDocuments server) of
        Just docState -> do
          let parseErrors = case docAST docState of
                Left err -> [Error (Range (Position 0 0) (Position 0 0)) 1 err]
                Right _ -> []
          let typeErrors = case docAST docState of
                Right ast -> case typeCheckModule ast of
                  Left err -> [Error (Range (Position 0 0) (Position 0 0)) 1 err]
                  Right _ -> []
                Left _ -> []
          let diagnostics = map errorToDiagnostic (parseErrors ++ typeErrors)
          let response = JSON.object
                [ ("diagnostics", JSON.toJSON diagnostics)
                ]
          return (response, server)
        Nothing -> return (JSON.object [("diagnostics", JSON.Array [])], server)
    Nothing -> return (JSON.object [("diagnostics", JSON.Array [])], server)

-- | Get completions at position
getCompletionsAtPosition :: PSModule -> Position -> T.Text -> [CompletionItem]
getCompletionsAtPosition module' pos content =
  let symbol = getSymbolAtPosition module' pos content
      context = getContextAtPosition module' pos content
      allDecls = getAllDeclarations module'
      suggestions = filterSuggestions symbol context allDecls
  in map declToCompletionItem suggestions

-- | Get hover information
getHoverInfo :: PSModule -> Position -> T.Text -> HoverInfo
getHoverInfo module' pos content =
  let symbol = getSymbolAtPosition module' pos content
      decl = findDeclaration module' symbol
      typeInfo = case decl of
        Just (PSValueDecl v) -> case valueType v of
          Just t -> formatType t
          Nothing -> "No type annotation"
        Just (PSDataDecl d) -> "data " <> dataName d
        Just (PSTypeDecl t) -> "type " <> typeName t
        Just (PSClassDecl c) -> "class " <> className c
        _ -> ""
      documentation = case decl of
        Just (PSValueDecl v) -> Just $ "Value: " <> valueName v
        Just (PSDataDecl d) -> Just $ "Data: " <> dataName d
        Just (PSTypeDecl t) -> Just $ "Type: " <> typeName t
        Just (PSClassDecl c) -> Just $ "Class: " <> className c
        _ -> Nothing
  in HoverInfo typeInfo documentation

-- | Find definition
findDefinition :: PSModule -> Position -> T.Text -> Location
findDefinition module' pos uri content =
  let symbol = getSymbolAtPosition module' pos content
      decl = findDeclaration module' symbol
      range = case decl of
        Just d -> getDeclarationRange d content
        Nothing -> Range (Position 0 0) (Position 0 0)
  in Location uri range

-- | Find references
findReferences :: PSModule -> Position -> T.Text -> T.Text -> [Location]
findReferences module' pos uri content =
  let symbol = getSymbolAtPosition module' pos content
      refs = findAllReferences module' symbol content
  in map (\r -> Location uri r) refs

-- | Get symbol at position
getSymbolAtPosition :: PSModule -> Position -> T.Text -> T.Text
getSymbolAtPosition module' (Position line col) content =
  let lines = T.lines content
      currentLine = if line < length lines then lines !! line else ""
      beforeCursor = T.take col currentLine
      afterCursor = T.drop col currentLine
      wordStart = T.dropWhileEnd (\c -> isIdentifierChar c) beforeCursor
      wordEnd = T.takeWhile isIdentifierChar afterCursor
      symbol = T.dropWhile (not . isIdentifierChar) wordStart <> wordEnd
  in symbol

-- | Get context at position
getContextAtPosition :: PSModule -> Position -> T.Text -> Context
getContextAtPosition module' pos content =
  let symbol = getSymbolAtPosition module' pos content
      line = positionLine pos
      col = positionCharacter pos
      lines = T.lines content
      contextLines = take 3 $ drop (max 0 (line - 1)) lines
  in Context symbol line col contextLines

-- | Filter suggestions based on context
filterSuggestions :: T.Text -> Context -> [PSDeclaration] -> [PSDeclaration]
filterSuggestions prefix context decls =
  let matches = filter (\d -> T.isPrefixOf prefix (declarationName d)) decls
      sorted = L.sortBy (\a b -> compare (declarationName a) (declarationName b)) matches
  in take 20 sorted

-- | Get all declarations from module
getAllDeclarations :: PSModule -> [PSDeclaration]
getAllDeclarations = moduleDeclarations

-- | Find declaration by name
findDeclaration :: PSModule -> T.Text -> Maybe PSDeclaration
findDeclaration module' name =
  L.find (\d -> declarationName d == name) (moduleDeclarations module')

-- | Find all references to symbol
findAllReferences :: PSModule -> T.Text -> T.Text -> [Range]
findAllReferences module' symbol content =
  let lines = T.lines content
      refs = concatMap (\(lineNum, line) ->
        let indices = findAllIndices symbol line
        in map (\col -> Range (Position lineNum col) (Position lineNum (col + T.length symbol))) indices
        ) (zip [0..] lines)
  in refs

-- | Find all indices of substring in text
findAllIndices :: T.Text -> T.Text -> [Int]
findAllIndices pattern text =
  let go acc idx =
        case T.findIndex (T.isPrefixOf pattern) (T.drop idx text) of
          Just pos -> go (acc ++ [idx + pos]) (idx + pos + 1)
          Nothing -> acc
  in go [] 0

-- | Get declaration name
declarationName :: PSDeclaration -> T.Text
declarationName (PSValueDecl decl) = valueName decl
declarationName (PSDataDecl decl) = dataName decl
declarationName (PSTypeDecl decl) = typeName decl
declarationName (PSClassDecl decl) = className decl
declarationName (PSInstanceDecl _) = ""

-- | Get declaration range
getDeclarationRange :: PSDeclaration -> T.Text -> Range
getDeclarationRange decl content =
  let name = declarationName decl
      lines = T.lines content
      found = L.findIndex (T.isInfixOf name) lines
  in case found of
    Just lineNum ->
      let line = lines !! lineNum
          col = case T.findIndex (T.isPrefixOf name) (T.tails line) of
            Just idx -> idx
            Nothing -> 0
      in Range (Position lineNum col) (Position lineNum (col + T.length name))
    Nothing -> Range (Position 0 0) (Position 0 0)

-- | Format type for display
formatType :: PSType -> T.Text
formatType (PSTypeVar v) = v
formatType (PSTypeCon n []) = n
formatType (PSTypeCon n args) = n <> " " <> T.unwords (map formatType args)
formatType (PSTypeArr a b) = formatType a <> " -> " <> formatType b
formatType (PSTypeRecord fields) = "{ " <> T.intercalate ", " (map (\(n, t) -> n <> " :: " <> formatType t) fields) <> " }"
formatType (PSTypeRow fields) = "(" <> T.intercalate ", " (map (\(n, t) -> n <> " :: " <> formatType t) fields) <> ")"
formatType (PSTypeApp f x) = formatType f <> " " <> formatType x

-- | Convert declaration to completion item
declToCompletionItem :: PSDeclaration -> CompletionItem
declToCompletionItem (PSValueDecl decl) = CompletionItem (valueName decl) 3 (valueType decl >>= Just . formatType)
declToCompletionItem (PSDataDecl decl) = CompletionItem (dataName decl) 7 (Just "data")
declToCompletionItem (PSTypeDecl decl) = CompletionItem (typeName decl) 5 (Just "type")
declToCompletionItem (PSClassDecl decl) = CompletionItem (className decl) 2 (Just "class")
declToCompletionItem _ = CompletionItem "" 0 Nothing

-- | Error to diagnostic conversion
errorToDiagnostic :: Error -> Diagnostic
errorToDiagnostic err = Diagnostic
  { diagnosticRange = errorRange err
  , diagnosticSeverity = errorSeverity err
  , diagnosticMessage = errorMessage err
  , diagnosticSource = "purescript-to-cpp23"
  }

-- | Check if character is identifier character
isIdentifierChar :: Char -> Bool
isIdentifierChar c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || 
                     (c >= '0' && c <= '9') || c == '_' || c == '\''

-- | Extract URI from LSP request
extractURI :: JSON.Value -> Maybe T.Text
extractURI v = do
  params <- JSON.parseMaybe (JSON..: "params") v
  textDoc <- JSON.parseMaybe (JSON..: "textDocument") params
  JSON.parseMaybe (JSON..: "uri") textDoc

-- | Extract text document and position
extractTextDocumentPosition :: JSON.Value -> Maybe (T.Text, Position)
extractTextDocumentPosition v = do
  params <- JSON.parseMaybe (JSON..: "params") v
  textDoc <- JSON.parseMaybe (JSON..: "textDocument") params
  uri <- JSON.parseMaybe (JSON..: "uri") textDoc
  position <- JSON.parseMaybe (JSON..: "position") params
  line <- JSON.parseMaybe (JSON..: "line") position
  character <- JSON.parseMaybe (JSON..: "character") position
  return (uri, Position line character)

-- | Extract text document
extractTextDocument :: JSON.Value -> Maybe (T.Text, T.Text, Int)
extractTextDocument v = do
  params <- JSON.parseMaybe (JSON..: "params") v
  textDoc <- JSON.parseMaybe (JSON..: "textDocument") params
  uri <- JSON.parseMaybe (JSON..: "uri") textDoc
  version <- JSON.parseMaybe (JSON..: "version") textDoc
  content <- JSON.parseMaybe (JSON..: "text") textDoc
  return (uri, content, version)

-- Helper types
data Position = Position { positionLine :: Int, positionCharacter :: Int }
  deriving (Show, Eq)

instance JSON.ToJSON Position where
  toJSON (Position line char) = JSON.object
    [ ("line", JSON.toJSON line)
    , ("character", JSON.toJSON char)
    ]

data Range = Range { rangeStart :: Position, rangeEnd :: Position }
  deriving (Show, Eq)

instance JSON.ToJSON Range where
  toJSON (Range start end) = JSON.object
    [ ("start", JSON.toJSON start)
    , ("end", JSON.toJSON end)
    ]

data Location = Location { locationUri :: T.Text, locationRange :: Range }
  deriving (Show, Eq)

instance JSON.ToJSON Location where
  toJSON (Location uri range) = JSON.object
    [ ("uri", JSON.toJSON uri)
    , ("range", JSON.toJSON range)
    ]

data CompletionItem = CompletionItem
  { completionLabel :: T.Text
  , completionKind :: Int
  , completionDetail :: Maybe T.Text
  }

instance JSON.ToJSON CompletionItem where
  toJSON (CompletionItem label kind detail) = JSON.object
    [ ("label", JSON.toJSON label)
    , ("kind", JSON.toJSON kind)
    , ("detail", JSON.toJSON detail)
    ]

data HoverInfo = HoverInfo
  { hoverType :: T.Text
  , hoverDocumentation :: Maybe T.Text
  }

instance JSON.ToJSON HoverInfo where
  toJSON (HoverInfo typ doc) = JSON.object
    [ ("contents", JSON.object
        [ ("kind", JSON.String "markdown")
        , ("value", JSON.String (typ <> maybe "" ("\n\n" <>) doc))
        ])
    ]

data Diagnostic = Diagnostic
  { diagnosticRange :: Range
  , diagnosticSeverity :: Int
  , diagnosticMessage :: T.Text
  , diagnosticSource :: T.Text
  }

instance JSON.ToJSON Diagnostic where
  toJSON (Diagnostic range severity message source) = JSON.object
    [ ("range", JSON.toJSON range)
    , ("severity", JSON.toJSON severity)
    , ("message", JSON.toJSON message)
    , ("source", JSON.toJSON source)
    ]

data Error = Error
  { errorRange :: Range
  , errorSeverity :: Int
  , errorMessage :: T.Text
  }

data Context = Context
  { contextSymbol :: T.Text
  , contextLine :: Int
  , contextColumn :: Int
  , contextLines :: [T.Text]
  }

