{-|
Module      : Bridge.WebSocket.Handlers.Files
Description : File context and terminal execution handlers
= File Handlers

JSON-RPC handlers for file operations including:
- File context management (add, list)
- File reading
- Terminal command execution
- Web search

== Error Codes

| Code | Meaning              |
|------|----------------------|
| 6001 | File context error   |
| 7001 | Terminal error       |
| 8001 | Web search error     |
| -32602 | Invalid params     |
-}
module Bridge.WebSocket.Handlers.Files
  ( -- * File Context Handlers
    handleFileContextAdd
  , handleFileContextList
  , handleFileRead
    -- * Terminal Handlers
  , handleTerminalExecute
    -- * Web Search Handlers
  , handleWebSearch
  ) where

import Prelude

import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect (Effect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))

import Bridge.WebSocket.Handlers.Types (HandlerContext, JsonRpcResponse, successResponse, errorResponse)
import Bridge.FFI.Node.Terminal as Terminal
import Bridge.FFI.Node.FileContext as FileContext
import Bridge.FFI.Node.Handlers as Handlers

-- ============================================================================
-- FFI
-- ============================================================================

foreign import decodeFileContextListRequest :: Maybe String -> Effect (Either String { sessionId :: String, filter :: Maybe String })
foreign import encodeFileContextListResponse :: Array FileContextEntry -> Effect String

type FileContextEntry = { path :: String, tokens :: Int, language :: String }

-- Web search module (to be implemented)
foreign import searchWeb :: { query :: String, limit :: Maybe Int } -> Aff (Either String WebSearchResponse)

type WebSearchResponse =
  { results :: Array { title :: String, url :: String, snippet :: String }
  , total :: Int
  }

-- ============================================================================
-- FILE CONTEXT HANDLERS
-- ============================================================================

{-| Handle file.context.add - Add file to context. -}
handleFileContextAdd :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleFileContextAdd ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeFileContextAddRequest paramsJson
      case decoded of
        Right request -> do
          result <- liftEffect $ FileContext.addFileToContext ctx.store request.path request.sessionId
          case result of
            Right response -> do
              responseJson <- liftEffect $ Handlers.encodeFileContextAddResponse response
              pure (successResponse Nothing responseJson)
            Left err -> pure (errorResponse Nothing 6001 err Nothing)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

{-| Handle file.context.list - List files in context. -}
handleFileContextList :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleFileContextList ctx params = do
  decoded <- liftEffect $ decodeFileContextListRequest params
  case decoded of
    Right request -> do
      files <- liftEffect $ FileContext.getContextFiles ctx.store request.sessionId request.filter
      responseJson <- liftEffect $ encodeFileContextListResponse files
      pure (successResponse Nothing responseJson)
    Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))

{-| Handle file.read - Read file content. -}
handleFileRead :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleFileRead ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeFileReadRequest paramsJson
      case decoded of
        Right request -> do
          result <- liftEffect $ FileContext.readFileContent request.path
          case result of
            Right content -> do
              response <- liftEffect $ Handlers.encodeFileReadResponse
                { success: true
                , content: Just content
                , error: Nothing
                }
              pure (successResponse Nothing response)
            Left err -> do
              response <- liftEffect $ Handlers.encodeFileReadResponse
                { success: false
                , content: Nothing
                , error: Just err
                }
              pure (successResponse Nothing response)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- ============================================================================
-- TERMINAL HANDLERS
-- ============================================================================

{-| Handle terminal.execute - Execute terminal command. -}
handleTerminalExecute :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleTerminalExecute ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeTerminalExecuteRequest paramsJson
      case decoded of
        Right request -> do
          result <- Terminal.executeCommand request.command request.cwd request.sessionId
          case result of
            Right response -> do
              responseJson <- liftEffect $ Handlers.encodeTerminalExecuteResponse response
              pure (successResponse Nothing responseJson)
            Left err -> pure (errorResponse Nothing 7001 err Nothing)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- ============================================================================
-- WEB SEARCH HANDLERS
-- ============================================================================

{-| Handle web.search - Execute web search. -}
handleWebSearch :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleWebSearch ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeWebSearchRequest paramsJson
      case decoded of
        Right request -> do
          result <- searchWeb request
          case result of
            Right response -> do
              responseJson <- liftEffect $ Handlers.encodeWebSearchResponse response
              pure (successResponse Nothing responseJson)
            Left err -> pure (errorResponse Nothing 8001 err Nothing)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))
