{-|
Module      : Opencode.Session.MessageV2
Description : Message V2 operations and conversions
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Message V2 Operations

Functions for message storage, retrieval, filtering, and LLM conversion.
Types are imported from MessageV2Types module.

== Coeffect Equation

@
  get       : MessageRef -> Graded Storage (WithParts)
  stream    : SessionID -> Graded Storage (Generator WithParts)
  fromError : Error × ProviderID -> MessageError
@

-}
module Opencode.Session.MessageV2
  ( -- * Re-exports from Types
    module Opencode.Session.MessageV2Types
    -- * Storage Functions
  , stream
  , parts
  , get
    -- * Filtering
  , filterCompacted
    -- * Error Conversion
  , fromError
  , isRetryableError
    -- * Model Message Conversion
  , toModelMessages
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Array as Array
import Data.String as String
import Effect.Aff (Aff)

-- Import types
import Opencode.Session.MessageV2Types

-- ════════════════════════════════════════════════════════════════════════════
-- STORAGE FUNCTIONS
-- ════════════════════════════════════════════════════════════════════════════

-- | Stream messages for a session (newest first)
-- | TODO: Implement with Storage module
stream :: String -> Aff (Array WithParts)
stream _sessionID = do
  -- In real impl, would query Storage.list(["message", sessionID])
  pure []

-- | Get parts for a message
-- | TODO: Implement with Storage module
parts :: String -> Aff (Array Part)
parts _messageID = do
  -- In real impl, would query Storage.list(["part", messageID])
  pure []

-- | Get a message with its parts
get :: { sessionID :: String, messageID :: String } -> Aff WithParts
get input = do
  ps <- parts input.messageID
  pure { info: dummyUserInfo input.sessionID input.messageID
       , parts: ps
       }
  where
    dummyUserInfo sid mid = InfoUser
      { id: mid
      , sessionID: sid
      , role: "user"
      , time: { created: 0.0 }
      , summary: Nothing
      , agent: "default"
      , model: { providerID: "openai", modelID: "gpt-4" }
      , system: Nothing
      , tools: Nothing
      , variant: Nothing
      }

-- ════════════════════════════════════════════════════════════════════════════
-- FILTERING
-- ════════════════════════════════════════════════════════════════════════════

-- | Filter messages, stopping at compaction point if found
filterCompacted :: Array WithParts -> Array WithParts
filterCompacted msgs =
  let findCompaction = Array.findIndex hasCompactionPart
      hasCompactionPart wp = Array.any isCompactionPart wp.parts
      isCompactionPart = case _ of
        PartCompaction _ -> true
        _ -> false
  in case findCompaction msgs of
    Nothing -> msgs
    Just idx -> Array.take (idx + 1) msgs

-- ════════════════════════════════════════════════════════════════════════════
-- ERROR CONVERSION
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert various error types to MessageError
fromError :: { error :: String, providerID :: String } -> MessageError
fromError input =
  if String.contains (String.Pattern "abort") (String.toLower input.error)
    then ErrorAborted { message: input.error }
  else if String.contains (String.Pattern "auth") (String.toLower input.error) ||
          String.contains (String.Pattern "401") input.error ||
          String.contains (String.Pattern "api key") (String.toLower input.error)
    then ErrorAuth { providerID: input.providerID, message: input.error }
  else if String.contains (String.Pattern "length") (String.toLower input.error) ||
          String.contains (String.Pattern "too long") (String.toLower input.error)
    then ErrorOutputLength {}
  else ErrorAPI
    { message: input.error
    , statusCode: Nothing
    , isRetryable: isRetryableError input.error
    , responseHeaders: Nothing
    , responseBody: Nothing
    , metadata: Nothing
    }

-- | Check if error is retryable
isRetryableError :: String -> Boolean
isRetryableError err =
  String.contains (String.Pattern "429") err ||
  String.contains (String.Pattern "500") err ||
  String.contains (String.Pattern "502") err ||
  String.contains (String.Pattern "503") err ||
  String.contains (String.Pattern "504") err ||
  String.contains (String.Pattern "ECONNRESET") err ||
  String.contains (String.Pattern "timeout") (String.toLower err)

-- ════════════════════════════════════════════════════════════════════════════
-- MODEL MESSAGE CONVERSION
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert WithParts array to model messages for LLM API
toModelMessages :: Array WithParts -> ModelRef -> Array UIMessage
toModelMessages input model = Array.mapMaybe convertMessage input
  where
    convertMessage :: WithParts -> Maybe UIMessage
    convertMessage wp = case wp.info of
      InfoUser u ->
        if Array.null wp.parts then Nothing
        else Just
          { id: u.id
          , role: "user"
          , parts: Array.mapMaybe convertUserPart wp.parts
          }
      InfoAssistant a ->
        if hasBlockingError a wp.parts then Nothing
        else
          let ps = Array.mapMaybe (convertAssistantPart (isDifferentModel a)) wp.parts
          in if Array.null ps then Nothing
             else Just { id: a.id, role: "assistant", parts: ps }
    
    hasBlockingError :: AssistantMessage -> Array Part -> Boolean
    hasBlockingError msg ps = case msg.error of
      Nothing -> false
      Just (ErrorAborted _) ->
        not (Array.any isContentPart ps)
      Just _ -> true
    
    isContentPart :: Part -> Boolean
    isContentPart = case _ of
      PartText _ -> true
      PartTool _ -> true
      PartReasoning _ -> true
      _ -> false
    
    isDifferentModel :: AssistantMessage -> Boolean
    isDifferentModel a =
      model.providerID <> "/" <> model.modelID /=
      a.providerID <> "/" <> a.modelID
    
    convertUserPart :: Part -> Maybe UIPart
    convertUserPart = case _ of
      PartText t ->
        if fromMaybe false t.ignored then Nothing
        else Just $ UIText { text: t.text, providerMetadata: Nothing }
      PartFile f ->
        if f.mime == "text/plain" || f.mime == "application/x-directory"
          then Nothing
          else Just $ UIFile { url: f.url, mediaType: f.mime, filename: f.filename }
      PartCompaction _ ->
        Just $ UIText { text: "What did we do so far?", providerMetadata: Nothing }
      PartSubtask _ ->
        Just $ UIText { text: "The following tool was executed by the user", providerMetadata: Nothing }
      _ -> Nothing
    
    convertAssistantPart :: Boolean -> Part -> Maybe UIPart
    convertAssistantPart differentModel = case _ of
      PartText t ->
        Just $ UIText
          { text: t.text
          , providerMetadata: if differentModel then Nothing else t.metadata
          }
      PartStepStart _ ->
        Just UIStepStart
      PartTool t ->
        Just $ convertToolPart t
      PartReasoning r ->
        Just $ UIReasoning { text: r.text }
      _ -> Nothing
    
    convertToolPart :: ToolPart -> UIPart
    convertToolPart t = case t.state of
      StateCompleted s ->
        let output = if isJust s.time.compacted
              then "[Old tool result content cleared]"
              else s.output
        in UIToolOutput
          { toolName: t.tool
          , state: "output-available"
          , toolCallId: t.callID
          , input: s.input
          , output: Just output
          , errorText: Nothing
          }
      StateError s ->
        UIToolOutput
          { toolName: t.tool
          , state: "output-error"
          , toolCallId: t.callID
          , input: s.input
          , output: Nothing
          , errorText: Just s.error
          }
      StatePending s ->
        UIToolOutput
          { toolName: t.tool
          , state: "output-error"
          , toolCallId: t.callID
          , input: s.input
          , output: Nothing
          , errorText: Just "[Tool execution was interrupted]"
          }
      StateRunning s ->
        UIToolOutput
          { toolName: t.tool
          , state: "output-error"
          , toolCallId: t.callID
          , input: s.input
          , output: Nothing
          , errorText: Just "[Tool execution was interrupted]"
          }
