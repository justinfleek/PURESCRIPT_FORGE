-- | Bridge API - File Operations
-- |
-- | File context, terminal execution, and file read operations.
-- |
-- | Coeffect Equation:
-- |   FileOps : WSClient -> Request -> Aff (Either Error Response)
-- |   with resource tracking: Connection^1 -o Result^1
-- |
-- | Module Coverage: file.context.add, file.context.list, file.read, terminal.execute
module Sidepanel.Api.Bridge.Files
  ( -- * File Context Operations
    addFileToContext
  , listFilesInContext
  , readFileContent
    -- * Terminal Operations
  , executeTerminalCommand
  ) where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Argonaut.Core (Json)
import Argonaut.Decode (class DecodeJson, decodeJson, (.:), (.:?))
import Argonaut.Encode (class EncodeJson, encodeJson)
import Sidepanel.WebSocket.Client (WSClient, request)
import Sidepanel.Api.Types (JsonRpcError)
import Sidepanel.Api.Bridge.Types
  ( FileContextAddRequest
  , FileContextAddResponse
  , FileContextListRequest
  , FileContextListResponse
  , FileInContext
  , FileReadRequest
  , FileReadResponse
  , TerminalExecuteRequest
  , TerminalExecuteResponse
  , printJsonDecodeError
  )

--------------------------------------------------------------------------------
-- | JSON Instances - File Context
--------------------------------------------------------------------------------

instance encodeFileContextAddRequest :: EncodeJson FileContextAddRequest where
  encodeJson req = encodeJson
    { path: req.path
    , sessionId: req.sessionId
    }

instance decodeFileContextAddResponse :: DecodeJson FileContextAddResponse where
  decodeJson json = do
    obj <- decodeJson json
    success <- obj .: "success"
    tokens <- obj .: "tokens"
    contextBudget <- obj .: "contextBudget"
    used <- contextBudget .: "used"
    total <- contextBudget .: "total"
    pure { success, tokens, contextBudget: { used, total } }

instance encodeFileContextListRequest :: EncodeJson FileContextListRequest where
  encodeJson req = encodeJson
    { sessionId: req.sessionId
    , filter: req.filter
    }

instance decodeFileInContext :: DecodeJson FileInContext where
  decodeJson json = do
    obj <- decodeJson json
    path <- obj .: "path"
    tokens <- obj .: "tokens"
    readAt <- obj .: "readAt"
    status <- obj .: "status"
    language <- obj .: "language"
    size <- obj .: "size"
    pure { path, tokens, readAt, status, language, size }

instance decodeFileContextListResponse :: DecodeJson FileContextListResponse where
  decodeJson json = do
    obj <- decodeJson json
    files <- obj .: "files"
    contextBudget <- obj .: "contextBudget"
    used <- contextBudget .: "used"
    total <- contextBudget .: "total"
    pure { files, contextBudget: { used, total } }

instance encodeFileReadRequest :: EncodeJson FileReadRequest where
  encodeJson req = encodeJson
    { path: req.path
    }

instance decodeFileReadResponse :: DecodeJson FileReadResponse where
  decodeJson json = do
    obj <- decodeJson json
    success <- obj .: "success"
    content <- obj .:? "content"
    error <- obj .:? "error"
    pure { success, content, error }

--------------------------------------------------------------------------------
-- | JSON Instances - Terminal
--------------------------------------------------------------------------------

instance encodeTerminalExecuteRequest :: EncodeJson TerminalExecuteRequest where
  encodeJson req = encodeJson
    { command: req.command
    , cwd: req.cwd
    , sessionId: req.sessionId
    }

instance decodeTerminalExecuteResponse :: DecodeJson TerminalExecuteResponse where
  decodeJson json = do
    obj <- decodeJson json
    success <- obj .: "success"
    output <- obj .:? "output"
    exitCode <- obj .:? "exitCode"
    pure { success, output, exitCode }

--------------------------------------------------------------------------------
-- | File Context Operations
--------------------------------------------------------------------------------

-- | Add file to context
addFileToContext :: WSClient -> FileContextAddRequest -> Aff (Either JsonRpcError FileContextAddResponse)
addFileToContext client req = do
  result <- request client "file.context.add" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError FileContextAddResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right r -> pure $ Right r

-- | List files in context
listFilesInContext :: WSClient -> FileContextListRequest -> Aff (Either JsonRpcError FileContextListResponse)
listFilesInContext client req = do
  result <- request client "file.context.list" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError FileContextListResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right r -> pure $ Right r

-- | Read file content
readFileContent :: WSClient -> FileReadRequest -> Aff (Either JsonRpcError FileReadResponse)
readFileContent client req = do
  result <- request client "file.read" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError FileReadResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right r -> pure $ Right r

--------------------------------------------------------------------------------
-- | Terminal Operations
--------------------------------------------------------------------------------

-- | Execute terminal command
executeTerminalCommand :: WSClient -> TerminalExecuteRequest -> Aff (Either JsonRpcError TerminalExecuteResponse)
executeTerminalCommand client req = do
  result <- request client "terminal.execute" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError TerminalExecuteResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right r -> pure $ Right r
