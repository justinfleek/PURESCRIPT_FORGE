-- | Bridge API - Lean4 Proof Assistant Operations
-- |
-- | Lean4 language server integration for formal verification.
-- |
-- | Coeffect Equation:
-- |   LeanOps : WSClient -> LeanRequest -> Aff (Either Error LeanResponse)
-- |   with proof tracking: Goal^n -o (Tactic^m * Goal^(n-k))
-- |   where tactics reduce goal count k <= n
-- |
-- | Module Coverage: lean.check, lean.goals, lean.applyTactic, lean.searchTheorems
module Sidepanel.Api.Bridge.Lean
  ( -- * Lean Operations
    checkLeanFile
  , getLeanGoals
  , applyLeanTactic
  , searchLeanTheorems
  ) where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Foldable (class Foldable)
import Foreign.Object as FO
import Argonaut.Core as AC
import Argonaut.Core (Json)
import Argonaut.Decode (class DecodeJson, decodeJson, (.:), (.:?))
import Argonaut.Encode (class EncodeJson, encodeJson, (:=), (:=?))
import Sidepanel.WebSocket.Client (WSClient, request)
import Sidepanel.Api.Types (JsonRpcError)
import Sidepanel.Api.Bridge.Types
  ( LeanCheckRequest
  , LeanCheckResponse
  , LeanDiagnostic
  , LeanGoalsRequest
  , LeanGoalsResponse
  , LeanGoal
  , LeanApplyTacticRequest
  , LeanApplyTacticResponse
  , LeanSearchTheoremsRequest
  , LeanSearchTheoremsResponse
  , TheoremResult
  , printJsonDecodeError
  )

--------------------------------------------------------------------------------
-- | JSON Instances - Lean Check
--------------------------------------------------------------------------------

instance encodeLeanCheckRequest :: EncodeJson LeanCheckRequest where
  encodeJson req = encodeJson { file: req.file }

instance decodeLeanDiagnostic :: DecodeJson LeanDiagnostic where
  decodeJson json = do
    obj <- decodeJson json
    severity <- obj .: "severity"
    message <- obj .: "message"
    range <- obj .: "range"
    start <- range .: "start"
    end <- range .: "end"
    startLine <- start .: "line"
    startCol <- start .: "col"
    endLine <- end .: "line"
    endCol <- end .: "col"
    pure
      { severity
      , message
      , range:
          { start: { line: startLine, col: startCol }
          , end: { line: endLine, col: endCol }
          }
      }

instance decodeLeanCheckResponse :: DecodeJson LeanCheckResponse where
  decodeJson json = do
    obj <- decodeJson json
    diagnostics <- obj .: "diagnostics"
    pure { diagnostics }

--------------------------------------------------------------------------------
-- | JSON Instances - Lean Goals
--------------------------------------------------------------------------------

instance encodeLeanGoalsRequest :: EncodeJson LeanGoalsRequest where
  encodeJson req = encodeJson
    { file: req.file
    , line: req.line
    , column: req.column
    }

instance decodeLeanGoal :: DecodeJson LeanGoal where
  decodeJson json = do
    obj <- decodeJson json
    type_ <- obj .: "type"
    context <- obj .: "context"
    pure { type_, context }

instance decodeLeanGoalsResponse :: DecodeJson LeanGoalsResponse where
  decodeJson json = do
    obj <- decodeJson json
    goals <- obj .: "goals"
    pure { goals }

--------------------------------------------------------------------------------
-- | JSON Instances - Apply Tactic
--------------------------------------------------------------------------------

instance encodeLeanApplyTacticRequest :: EncodeJson LeanApplyTacticRequest where
  encodeJson req = 
    let baseFields = 
          [ "file" := req.file
          , "line" := req.line
          , "column" := req.column
          , "tactic" := req.tactic
          ]
        optionalFields = case req.goalIndex of
          Just idx -> [ "goalIndex" := idx ]
          Nothing -> []
    in encodeJson $ FO.fromFoldable (baseFields <> optionalFields)

instance decodeLeanApplyTacticResponse :: DecodeJson LeanApplyTacticResponse where
  decodeJson json = do
    obj <- decodeJson json
    success <- obj .: "success"
    message <- obj .:? "message"
    goals <- obj .: "goals"
    pure { success, message, goals }

--------------------------------------------------------------------------------
-- | JSON Instances - Search Theorems
--------------------------------------------------------------------------------

instance encodeLeanSearchTheoremsRequest :: EncodeJson LeanSearchTheoremsRequest where
  encodeJson req =
    let baseFields = [ "query" := req.query ]
        limitField = case req.limit of
          Just l -> [ "limit" := l ]
          Nothing -> []
        fileField = case req.file of
          Just f -> [ "file" := f ]
          Nothing -> []
    in encodeJson $ FO.fromFoldable (baseFields <> limitField <> fileField)

instance decodeTheoremResult :: DecodeJson TheoremResult where
  decodeJson json = do
    obj <- decodeJson json
    name <- obj .: "name"
    statement <- obj .: "statement"
    file <- obj .: "file"
    line <- obj .: "line"
    description <- obj .:? "description"
    pure { name, statement, file, line, description }

instance decodeLeanSearchTheoremsResponse :: DecodeJson LeanSearchTheoremsResponse where
  decodeJson json = do
    obj <- decodeJson json
    theorems <- obj .: "theorems"
    total <- obj .: "total"
    pure { theorems, total }

--------------------------------------------------------------------------------
-- | Lean Operations
--------------------------------------------------------------------------------

-- | Check Lean file for diagnostics
checkLeanFile :: WSClient -> LeanCheckRequest -> Aff (Either JsonRpcError LeanCheckResponse)
checkLeanFile client req = do
  result <- request client "lean.check" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError LeanCheckResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right r -> pure $ Right r

-- | Get Lean goals at cursor position
getLeanGoals :: WSClient -> LeanGoalsRequest -> Aff (Either JsonRpcError LeanGoalsResponse)
getLeanGoals client req = do
  result <- request client "lean.goals" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError LeanGoalsResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right r -> pure $ Right r

-- | Apply Lean tactic at cursor position
applyLeanTactic :: WSClient -> LeanApplyTacticRequest -> Aff (Either JsonRpcError LeanApplyTacticResponse)
applyLeanTactic client req = do
  result <- request client "lean.applyTactic" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError LeanApplyTacticResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right r -> pure $ Right r

-- | Search Lean theorems by query
searchLeanTheorems :: WSClient -> LeanSearchTheoremsRequest -> Aff (Either JsonRpcError LeanSearchTheoremsResponse)
searchLeanTheorems client req = do
  result <- request client "lean.searchTheorems" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError LeanSearchTheoremsResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right r -> pure $ Right r
