-- | File Handlers - File context, terminal execution, web search
module Bridge.WebSocket.Handlers.Files
  ( handleFileContextAdd
  , handleFileContextList
  , handleFileRead
  , handleTerminalExecute
  , handleWebSearch
  ) where

import Prelude
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Effect.Class (liftEffect)
import Effect (Effect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Bridge.WebSocket.Handlers.Types (HandlerContext, JsonRpcResponse, successResponse, errorResponse)
import Bridge.FFI.Node.Terminal as Terminal
import Bridge.FFI.Node.FileContext as FileContext
import Bridge.FFI.Node.Handlers as Handlers

-- | FFI declarations (top-level)
foreign import searchWebImpl :: { query :: String, maxResults :: Maybe Int, sessionId :: Maybe String } -> EffectFnAff (Either String String)

-- | Handle file.context.add
handleFileContextAdd :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleFileContextAdd ctx params =
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

-- | Handle file.context.list
handleFileContextList :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleFileContextList ctx params = do
  decoded <- liftEffect $ Handlers.decodeFileContextListRequest params
  case decoded of
    Right request -> do
      files <- liftEffect $ FileContext.getContextFiles ctx.store request.sessionId request.filter
      responseJson <- liftEffect $ Handlers.encodeFileContextListResponse files
      pure (successResponse Nothing responseJson)
    Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))

-- | Handle file.read
handleFileRead :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleFileRead _ctx params =
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeFileReadRequest paramsJson
      case decoded of
        Right request -> do
          result <- liftEffect $ FileContext.readFileContent request.path
          case result of
            Right content -> do
              response <- liftEffect $ Handlers.encodeFileReadResponse
                { success: true, content: Just content, error: Nothing }
              pure (successResponse Nothing response)
            Left err -> do
              response <- liftEffect $ Handlers.encodeFileReadResponse
                { success: false, content: Nothing, error: Just err }
              pure (successResponse Nothing response)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- | Handle terminal.execute
handleTerminalExecute :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleTerminalExecute _ctx params =
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

-- | Handle web.search
handleWebSearch :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleWebSearch _ctx params =
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeWebSearchRequest paramsJson
      case decoded of
        Right request -> do
          result <- fromEffectFnAff $ searchWebImpl request
          case result of
            Right responseJson -> pure (successResponse Nothing responseJson)
            Left err -> pure (errorResponse Nothing 8001 err Nothing)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))
