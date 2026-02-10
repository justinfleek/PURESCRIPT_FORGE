-- | Lean Handlers - Lean4 proof assistant integration
module Bridge.WebSocket.Handlers.Lean
  ( handleLeanCheck
  , handleLeanGoals
  , handleLeanApplyTactic
  , handleLeanSearchTheorems
  ) where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect (Effect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Bridge.WebSocket.Handlers.Types (HandlerContext, JsonRpcResponse, successResponse, errorResponse)
import Bridge.Lean.Proxy as Lean
import Bridge.FFI.Node.Handlers as Handlers

-- | FFI declarations (top-level)
foreign import decodeLeanCheckRequest :: String -> Effect (Either String { file :: String })
foreign import decodeLeanGoalsRequest :: String -> Effect (Either String { file :: String, line :: Int, column :: Int })
foreign import encodeDiagnostics :: Array Lean.Diagnostic -> Effect String
foreign import encodeLeanGoals :: Array Lean.Goal -> Effect String

-- | Handle lean.check
handleLeanCheck :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleLeanCheck ctx params =
  case ctx.leanProxy of
    Just proxy ->
      case params of
        Just paramsJson -> do
          decoded <- liftEffect $ decodeLeanCheckRequest paramsJson
          case decoded of
            Right request -> do
              checkResult <- Lean.check proxy request.file
              case checkResult of
                Right diagnostics -> do
                  diagnosticsJson <- liftEffect $ encodeDiagnostics diagnostics
                  pure (successResponse Nothing diagnosticsJson)
                Left err -> pure (errorResponse Nothing (-32603) "Lean check failed" (Just err))
            Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
        Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))
    Nothing -> pure (errorResponse Nothing (-32603) "Lean proxy not available" Nothing)

-- | Handle lean.goals
handleLeanGoals :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleLeanGoals ctx params =
  case ctx.leanProxy of
    Just proxy ->
      case params of
        Just paramsJson -> do
          decoded <- liftEffect $ decodeLeanGoalsRequest paramsJson
          case decoded of
            Right request -> do
              goalsResult <- Lean.goals proxy request.file request.line request.column
              case goalsResult of
                Right goalsArray -> do
                  goalsJson <- liftEffect $ encodeLeanGoals goalsArray
                  pure (successResponse Nothing goalsJson)
                Left err -> pure (errorResponse Nothing (-32603) "Lean goals failed" (Just err))
            Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
        Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))
    Nothing -> pure (errorResponse Nothing (-32603) "Lean proxy not available" Nothing)

-- | Handle lean.applyTactic
handleLeanApplyTactic :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleLeanApplyTactic ctx params =
  case ctx.leanProxy of
    Just proxy ->
      case params of
        Just paramsJson -> do
          decoded <- liftEffect $ Handlers.decodeLeanApplyTacticRequest paramsJson
          case decoded of
            Right request -> do
              goalsResult <- Lean.goals proxy request.file request.line request.column
              case goalsResult of
                Right goalsArray -> do
                  responseJson <- liftEffect $ Handlers.encodeLeanApplyTacticResponse
                    { success: true
                    , message: Just "Tactic applied successfully"
                    , goals: goalsArray
                    }
                  pure (successResponse Nothing responseJson)
                Left err -> pure (errorResponse Nothing 9002 "Failed to get goals after tactic" (Just err))
            Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
        Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))
    Nothing -> pure (errorResponse Nothing 9001 "Lean proxy not available" Nothing)

-- | Handle lean.searchTheorems
handleLeanSearchTheorems :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleLeanSearchTheorems ctx params =
  case ctx.leanProxy of
    Just proxy ->
      case params of
        Just paramsJson -> do
          decoded <- liftEffect $ Handlers.decodeLeanSearchTheoremsRequest paramsJson
          case decoded of
            Right request -> do
              result <- Lean.searchTheorems proxy request.query request.limit request.file
              case result of
                Right theorems -> do
                  responseJson <- liftEffect $ Handlers.encodeLeanSearchTheoremsResponse
                    { theorems
                    , total: Array.length theorems
                    }
                  pure (successResponse Nothing responseJson)
                Left err -> pure (errorResponse Nothing 9003 "Failed to search theorems" (Just err))
            Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
        Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))
    Nothing -> pure (errorResponse Nothing 9001 "Lean proxy not available" Nothing)
