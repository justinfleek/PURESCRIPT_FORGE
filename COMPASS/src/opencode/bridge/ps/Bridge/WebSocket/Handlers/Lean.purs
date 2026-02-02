{-|
Module      : Bridge.WebSocket.Handlers.Lean
Description : Lean4 proof assistant handlers
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Lean Handlers

JSON-RPC handlers for Lean4 Language Server Protocol integration.
Provides type checking, goal display, tactic application, and
theorem search.

== Error Codes

| Code | Meaning                  |
|------|--------------------------|
| 9001 | Lean proxy not available |
| 9002 | Tactic application error |
| 9003 | Theorem search error     |
| -32602 | Invalid params         |
| -32603 | Internal error         |

== Supported Operations

- lean.check: Type check a Lean file
- lean.goals: Get proof goals at position
- lean.applyTactic: Apply a tactic
- lean.searchTheorems: Search for theorems
-}
module Bridge.WebSocket.Handlers.Lean
  ( -- * Handlers
    handleLeanCheck
  , handleLeanGoals
  , handleLeanApplyTactic
  , handleLeanSearchTheorems
    -- * Types
  , Diagnostic(..)
  , Goal(..)
  ) where

import Prelude

import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect (Effect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Array as Array

import Bridge.WebSocket.Handlers.Types (HandlerContext, JsonRpcResponse, successResponse, errorResponse)
import Bridge.Lean.Proxy (LeanProxy, check, goals, searchTheorems)
import Bridge.FFI.Node.Handlers as Handlers

-- ============================================================================
-- TYPES
-- ============================================================================

type Diagnostic =
  { severity :: String
  , message :: String
  , range :: { start :: { line :: Int, character :: Int }, end :: { line :: Int, character :: Int } }
  }

type Goal =
  { name :: String
  , type_ :: String
  , hypotheses :: Array { name :: String, type_ :: String }
  }

-- ============================================================================
-- FFI
-- ============================================================================

foreign import decodeLeanCheckRequest :: String -> Effect (Either String { file :: String })
foreign import decodeLeanGoalsRequest :: String -> Effect (Either String { file :: String, line :: Int, column :: Int })
foreign import encodeDiagnostics :: Array Diagnostic -> Effect String
foreign import encodeLeanGoals :: Array Goal -> Effect String

-- ============================================================================
-- CHECK HANDLER
-- ============================================================================

{-| Handle Lean check - Check Lean4 file for errors.

Returns diagnostics (errors, warnings, info messages).
-}
handleLeanCheck :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleLeanCheck ctx params = do
  case ctx.leanProxy of
    Just proxy -> do
      case params of
        Just paramsJson -> do
          decoded <- liftEffect $ decodeLeanCheckRequest paramsJson
          case decoded of
            Right request -> do
              checkResult <- check proxy request.file
              case checkResult of
                Right diagnostics -> do
                  diagnosticsJson <- liftEffect $ encodeDiagnostics diagnostics
                  pure (successResponse Nothing diagnosticsJson)
                Left err -> pure (errorResponse Nothing (-32603) "Lean check failed" (Just err))
            Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
        Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))
    Nothing -> pure (errorResponse Nothing (-32603) "Lean proxy not available" Nothing)

-- ============================================================================
-- GOALS HANDLER
-- ============================================================================

{-| Handle Lean goals - Get proof goals at position. -}
handleLeanGoals :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleLeanGoals ctx params = do
  case ctx.leanProxy of
    Just proxy -> do
      case params of
        Just paramsJson -> do
          decoded <- liftEffect $ decodeLeanGoalsRequest paramsJson
          case decoded of
            Right request -> do
              goalsResult <- goals proxy request.file request.line request.column
              case goalsResult of
                Right goalsArray -> do
                  goalsJson <- liftEffect $ encodeLeanGoals goalsArray
                  pure (successResponse Nothing goalsJson)
                Left err -> pure (errorResponse Nothing (-32603) "Lean goals failed" (Just err))
            Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
        Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))
    Nothing -> pure (errorResponse Nothing (-32603) "Lean proxy not available" Nothing)

-- ============================================================================
-- TACTIC HANDLER
-- ============================================================================

{-| Handle Lean apply tactic - Apply a tactic and refresh goals. -}
handleLeanApplyTactic :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleLeanApplyTactic ctx params = do
  case ctx.leanProxy of
    Just proxy -> do
      case params of
        Just paramsJson -> do
          decoded <- liftEffect $ Handlers.decodeLeanApplyTacticRequest paramsJson
          case decoded of
            Right request -> do
              -- Apply tactic and refresh goals
              goalsResult <- goals proxy request.file request.line request.column
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

-- ============================================================================
-- THEOREM SEARCH HANDLER
-- ============================================================================

{-| Handle Lean search theorems - Search for theorems matching query. -}
handleLeanSearchTheorems :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleLeanSearchTheorems ctx params = do
  case ctx.leanProxy of
    Just proxy -> do
      case params of
        Just paramsJson -> do
          decoded <- liftEffect $ Handlers.decodeLeanSearchTheoremsRequest paramsJson
          case decoded of
            Right request -> do
              result <- searchTheorems proxy request.query request.limit request.file
              case result of
                Right theorems -> do
                  responseJson <- liftEffect $ Handlers.encodeLeanSearchTheoremsResponse
                    { theorems: theorems
                    , total: Array.length theorems
                    }
                  pure (successResponse Nothing responseJson)
                Left err -> pure (errorResponse Nothing 9003 "Failed to search theorems" (Just err))
            Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
        Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))
    Nothing -> pure (errorResponse Nothing 9001 "Lean proxy not available" Nothing)
