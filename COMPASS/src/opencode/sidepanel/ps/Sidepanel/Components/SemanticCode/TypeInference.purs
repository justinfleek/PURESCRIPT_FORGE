{-|
Module      : Sidepanel.Components.SemanticCode.TypeInference
Description : Type inference and display
Provides type inference information for hover, completion, and display.
-}
module Sidepanel.Components.SemanticCode.TypeInference where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.Argonaut (Json, decodeJson, (.:), (.:?))
import Effect.Aff (Aff)
import Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes (Position)
import Sidepanel.Components.SemanticCode.TypeInferenceTypes
  ( TypeInfo
  , TypeKind(..)
  , InferredType
  )
import Tool.Lsp as Lsp

-- | Get type at position using LSP hover
getTypeAtPosition :: String -> Position -> Aff (Maybe TypeInfo)
getTypeAtPosition fileUri position = do
  -- Use LSP hover operation to get type information
  let lspPosition = { line: position.line, character: position.character }
  result <- Lsp.callLspServer "hover" fileUri lspPosition
  
  case result of
    [] -> pure Nothing
    jsonArray -> do
      -- Parse LSP hover response
      -- LSP hover returns: { contents: string | MarkedString[], range?: Range }
      case Array.head jsonArray of
        Nothing -> pure Nothing
        Just json -> case decodeJson json of
          Left _ -> pure Nothing
          Right obj -> do
            -- Extract contents from hover response
            contentsM <- obj .:? "contents"
            case contentsM of
              Nothing -> pure Nothing
              Just contents -> do
                -- Parse type from hover content
                let typeStr = extractTypeFromHoverContent contents
                pure $ Just
                  { kind: PrimitiveType
                  , name: Just typeStr
                  , signature: Nothing
                  , parameters: []
                  }
  where
    extractTypeFromHoverContent :: Json -> String
    extractTypeFromHoverContent json =
      -- Try to extract type string from hover content
      -- LSP hover can return string or MarkedString array
      case decodeJson json of
        Left _ -> "unknown"
        Right str -> str
        -- If it's an array, extract from first element
        -- (simplified - would need proper MarkedString parsing)

-- | Infer type from expression using LSP
inferType :: String -> Aff (Maybe InferredType)
inferType expression = do
  -- Use LSP to infer type from expression
  -- This would typically require:
  -- 1. Creating a temporary file with the expression
  -- 2. Calling LSP hover/completion at the expression position
  -- 3. Extracting type information
  -- For now, return placeholder - would need file context
  pure Nothing
  -- Full implementation would:
  -- let tempFile = createTempFile expression
  -- position <- getExpressionPosition tempFile
  -- typeInfo <- getTypeAtPosition tempFile position
  -- deleteTempFile tempFile
  -- pure typeInfo

-- | Get type signature for symbol using LSP
getTypeSignature :: String -> String -> Aff (Maybe String)
getTypeSignature fileUri symbolName = do
  -- First, find symbol position using documentSymbol
  -- Then use hover at that position to get type signature
  let lspPosition = { line: 0, character: 0 }  -- Start search from beginning
  symbolResult <- Lsp.callLspServer "documentSymbol" fileUri lspPosition
  
  case result of
    [] -> pure Nothing
    jsonArray -> do
      -- Find symbol matching symbolName
      let matchingSymbol = Array.find (\json -> 
            case decodeJson json of
              Left _ -> false
              Right obj -> 
                case obj .:? "name" of
                  Nothing -> false
                  Just nameJson -> 
                    case decodeJson nameJson of
                      Left _ -> false
                      Right name -> name == symbolName
          ) jsonArray
      
      case matchingSymbol of
        Nothing -> pure Nothing
        Just symbolJson -> do
          -- Extract type signature from symbol info
          case decodeJson symbolJson of
            Left _ -> pure Nothing
            Right obj -> do
              -- LSP SymbolInformation has: name, kind, location, containerName
              -- Type signature would be in detail or would need hover call
              nameM <- obj .:? "name" >>= case _ of
                Nothing -> pure Nothing
                Just n -> case decodeJson n of
                  Left _ -> Nothing
                  Right name -> Just name
              
              detailM <- obj .:? "detail" >>= case _ of
                Nothing -> pure Nothing
                Just d -> case decodeJson d of
                  Left _ -> Nothing
                  Right detail -> Just detail
              
              -- If detail not found, try hover at symbol location
              case detailM of
                Just detail -> pure $ Just detail
                Nothing -> do
                  -- Get symbol location and use hover
                  locationM <- obj .:? "location"
                  case locationM of
                    Nothing -> pure nameM
                    Just locJson -> case decodeJson locJson of
                      Left _ -> pure nameM
                      Right loc -> do
                        -- Extract line and character from location
                        -- LSP location format: { uri: string, range: { start: { line, character }, end: {...} } }
                        rangeM <- loc .:? "range"
                        case rangeM of
                          Nothing -> pure nameM
                          Just rangeJson -> case decodeJson rangeJson of
                            Left _ -> pure nameM
                            Right range -> do
                              startM <- range .:? "start"
                              case startM of
                                Nothing -> pure nameM
                                Just startJson -> case decodeJson startJson of
                                  Left _ -> pure nameM
                                  Right start -> do
                                    lineM <- start .:? "line" >>= decodeJson
                                    charM <- start .:? "character" >>= decodeJson
                                    case lineM, charM of
                                      Just line, Just char -> do
                                        -- Use hover at symbol position
                                        hoverResult <- Lsp.callLspServer "hover" fileUri { line, character: char }
                                        case Array.head hoverResult of
                                          Nothing -> pure nameM
                                          Just hoverJson -> case decodeJson hoverJson of
                                            Left _ -> pure nameM
                                            Right hoverObj -> do
                                              contentsM <- hoverObj .:? "contents"
                                              case contentsM of
                                                Nothing -> pure nameM
                                                Just contents -> case decodeJson contents of
                                                  Left _ -> pure nameM
                                                  Right contentsStr -> pure $ Just contentsStr
                                      _, _ -> pure nameM

-- | Format type for display
formatType :: InferredType -> String
formatType type_ = case type_ of
  { kind: FunctionType, signature: Just sig } -> sig
  { kind: PrimitiveType, name: Just name } -> name
  { kind: GenericType, name: Just name, parameters: params } ->
    name <> "<" <> String.joinWith ", " (Array.map formatType params) <> ">"
  { kind: UnionType, types: types } ->
    String.joinWith " | " (Array.map formatType types)
  { kind: IntersectionType, types: types } ->
    String.joinWith " & " (Array.map formatType types)
  _ -> "unknown"
