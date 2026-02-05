{-|
Module      : Opencode.Session.MessageV2Types
Description : Type definitions for Message V2 format
= Message V2 Types

Extracted type definitions for OpenCode's message-v2.ts format.
Contains all part types, error types, and message structures.

== Part Type Hierarchy

@
  Part = TextPart | ReasoningPart | FilePart | ToolPart
       | StepStartPart | StepFinishPart | SnapshotPart
       | PatchPart | AgentPart | SubtaskPart | RetryPart
       | CompactionPart
@

-}
module Opencode.Session.MessageV2Types
  ( -- * Error Types
    OutputLengthError
  , AbortedError
  , AuthError
  , APIError
  , MessageError(..)
    -- * Part Base
  , PartBase
    -- * Part Types
  , SnapshotPart
  , PatchPart
  , TextPart
  , ReasoningPart
  , FilePart
  , FilePartSource(..)
  , FileSource
  , SymbolSource
  , ResourceSource
  , FilePartSourceText
  , AgentPart
  , CompactionPart
  , SubtaskPart
  , RetryPart
  , StepStartPart
  , StepFinishPart
  , StepTokens
    -- * Tool Parts
  , ToolStatePending
  , ToolStateRunning
  , ToolStateCompleted
  , ToolStateError
  , ToolState(..)
  , ToolPart
    -- * Part Union
  , Part(..)
  , partId
  , partMessageId
  , partSessionId
    -- * Message Types
  , UserMessage
  , AssistantMessage
  , Info(..)
  , infoId
  , infoSessionId
  , WithParts
    -- * Model Summary
  , ModelRef
  , MessageSummary
  , FileDiff
    -- * UI Types
  , UIMessage
  , UIPart(..)
  ) where

import Prelude
import Data.Maybe (Maybe)

-- ════════════════════════════════════════════════════════════════════════════
-- ERROR TYPES
-- ════════════════════════════════════════════════════════════════════════════

type OutputLengthError = {}

type AbortedError = { message :: String }

type AuthError =
  { providerID :: String
  , message :: String
  }

type APIError =
  { message :: String
  , statusCode :: Maybe Int
  , isRetryable :: Boolean
  , responseHeaders :: Maybe (Array { key :: String, value :: String })
  , responseBody :: Maybe String
  , metadata :: Maybe (Array { key :: String, value :: String })
  }

data MessageError
  = ErrorAuth AuthError
  | ErrorAPI APIError
  | ErrorOutputLength OutputLengthError
  | ErrorAborted AbortedError
  | ErrorUnknown { message :: String }

-- ════════════════════════════════════════════════════════════════════════════
-- PART BASE
-- ════════════════════════════════════════════════════════════════════════════

type PartBase =
  { id :: String
  , sessionID :: String
  , messageID :: String
  }

-- ════════════════════════════════════════════════════════════════════════════
-- SNAPSHOT & PATCH PARTS
-- ════════════════════════════════════════════════════════════════════════════

type SnapshotPart =
  { id :: String
  , sessionID :: String
  , messageID :: String
  , snapshot :: String
  }

type PatchPart =
  { id :: String
  , sessionID :: String
  , messageID :: String
  , hash :: String
  , files :: Array String
  }

-- ════════════════════════════════════════════════════════════════════════════
-- TEXT & REASONING PARTS
-- ════════════════════════════════════════════════════════════════════════════

type TextPart =
  { id :: String
  , sessionID :: String
  , messageID :: String
  , text :: String
  , synthetic :: Maybe Boolean
  , ignored :: Maybe Boolean
  , time :: Maybe { start :: Number, end :: Maybe Number }
  , metadata :: Maybe (Array { key :: String, value :: String })
  }

type ReasoningPart =
  { id :: String
  , sessionID :: String
  , messageID :: String
  , text :: String
  , metadata :: Maybe (Array { key :: String, value :: String })
  , time :: { start :: Number, end :: Maybe Number }
  }

-- ════════════════════════════════════════════════════════════════════════════
-- FILE PARTS
-- ════════════════════════════════════════════════════════════════════════════

type FilePartSourceText =
  { value :: String
  , start :: Int
  , end :: Int
  }

type FileSource =
  { text :: FilePartSourceText
  , path :: String
  }

type SymbolSource =
  { text :: FilePartSourceText
  , path :: String
  , range :: { start :: { line :: Int, character :: Int }
             , end :: { line :: Int, character :: Int }
             }
  , name :: String
  , kind :: Int
  }

type ResourceSource =
  { text :: FilePartSourceText
  , clientName :: String
  , uri :: String
  }

data FilePartSource
  = SourceFile FileSource
  | SourceSymbol SymbolSource
  | SourceResource ResourceSource

type FilePart =
  { id :: String
  , sessionID :: String
  , messageID :: String
  , mime :: String
  , filename :: Maybe String
  , url :: String
  , source :: Maybe FilePartSource
  }

-- ════════════════════════════════════════════════════════════════════════════
-- AGENT & SUBTASK PARTS
-- ════════════════════════════════════════════════════════════════════════════

type AgentPart =
  { id :: String
  , sessionID :: String
  , messageID :: String
  , name :: String
  , source :: Maybe FilePartSourceText
  }

type ModelRef =
  { providerID :: String
  , modelID :: String
  }

type SubtaskPart =
  { id :: String
  , sessionID :: String
  , messageID :: String
  , prompt :: String
  , description :: String
  , agent :: String
  , model :: Maybe ModelRef
  , command :: Maybe String
  }

type CompactionPart =
  { id :: String
  , sessionID :: String
  , messageID :: String
  , auto :: Boolean
  }

type RetryPart =
  { id :: String
  , sessionID :: String
  , messageID :: String
  , attempt :: Int
  , error :: APIError
  , time :: { created :: Number }
  }

-- ════════════════════════════════════════════════════════════════════════════
-- STEP PARTS
-- ════════════════════════════════════════════════════════════════════════════

type StepStartPart =
  { id :: String
  , sessionID :: String
  , messageID :: String
  , snapshot :: Maybe String
  }

type StepTokens =
  { input :: Int
  , output :: Int
  , reasoning :: Int
  , cache :: { read :: Int, write :: Int }
  }

type StepFinishPart =
  { id :: String
  , sessionID :: String
  , messageID :: String
  , reason :: String
  , snapshot :: Maybe String
  , cost :: Number
  , tokens :: StepTokens
  }

-- ════════════════════════════════════════════════════════════════════════════
-- TOOL PARTS
-- ════════════════════════════════════════════════════════════════════════════

type ToolStatePending =
  { input :: Array { key :: String, value :: String }
  , raw :: String
  }

type ToolStateRunning =
  { input :: Array { key :: String, value :: String }
  , title :: Maybe String
  , metadata :: Maybe (Array { key :: String, value :: String })
  , time :: { start :: Number }
  }

type ToolStateCompleted =
  { input :: Array { key :: String, value :: String }
  , output :: String
  , title :: String
  , metadata :: Array { key :: String, value :: String }
  , time :: { start :: Number, end :: Number, compacted :: Maybe Number }
  , attachments :: Maybe (Array FilePart)
  }

type ToolStateError =
  { input :: Array { key :: String, value :: String }
  , error :: String
  , metadata :: Maybe (Array { key :: String, value :: String })
  , time :: { start :: Number, end :: Number }
  }

data ToolState
  = StatePending ToolStatePending
  | StateRunning ToolStateRunning
  | StateCompleted ToolStateCompleted
  | StateError ToolStateError

type ToolPart =
  { id :: String
  , sessionID :: String
  , messageID :: String
  , callID :: String
  , tool :: String
  , state :: ToolState
  , metadata :: Maybe (Array { key :: String, value :: String })
  }

-- ════════════════════════════════════════════════════════════════════════════
-- PART UNION
-- ════════════════════════════════════════════════════════════════════════════

data Part
  = PartText TextPart
  | PartReasoning ReasoningPart
  | PartFile FilePart
  | PartTool ToolPart
  | PartStepStart StepStartPart
  | PartStepFinish StepFinishPart
  | PartSnapshot SnapshotPart
  | PartPatch PatchPart
  | PartAgent AgentPart
  | PartSubtask SubtaskPart
  | PartRetry RetryPart
  | PartCompaction CompactionPart

partId :: Part -> String
partId = case _ of
  PartText p -> p.id
  PartReasoning p -> p.id
  PartFile p -> p.id
  PartTool p -> p.id
  PartStepStart p -> p.id
  PartStepFinish p -> p.id
  PartSnapshot p -> p.id
  PartPatch p -> p.id
  PartAgent p -> p.id
  PartSubtask p -> p.id
  PartRetry p -> p.id
  PartCompaction p -> p.id

partMessageId :: Part -> String
partMessageId = case _ of
  PartText p -> p.messageID
  PartReasoning p -> p.messageID
  PartFile p -> p.messageID
  PartTool p -> p.messageID
  PartStepStart p -> p.messageID
  PartStepFinish p -> p.messageID
  PartSnapshot p -> p.messageID
  PartPatch p -> p.messageID
  PartAgent p -> p.messageID
  PartSubtask p -> p.messageID
  PartRetry p -> p.messageID
  PartCompaction p -> p.messageID

partSessionId :: Part -> String
partSessionId = case _ of
  PartText p -> p.sessionID
  PartReasoning p -> p.sessionID
  PartFile p -> p.sessionID
  PartTool p -> p.sessionID
  PartStepStart p -> p.sessionID
  PartStepFinish p -> p.sessionID
  PartSnapshot p -> p.sessionID
  PartPatch p -> p.sessionID
  PartAgent p -> p.sessionID
  PartSubtask p -> p.sessionID
  PartRetry p -> p.sessionID
  PartCompaction p -> p.sessionID

-- ════════════════════════════════════════════════════════════════════════════
-- MESSAGE TYPES
-- ════════════════════════════════════════════════════════════════════════════

type FileDiff =
  { path :: String
  , added :: Int
  , removed :: Int
  , status :: String
  }

type MessageSummary =
  { title :: Maybe String
  , body :: Maybe String
  , diffs :: Array FileDiff
  }

type UserMessage =
  { id :: String
  , sessionID :: String
  , role :: String
  , time :: { created :: Number }
  , summary :: Maybe MessageSummary
  , agent :: String
  , model :: ModelRef
  , system :: Maybe String
  , tools :: Maybe (Array { name :: String, enabled :: Boolean })
  , variant :: Maybe String
  }

type AssistantMessage =
  { id :: String
  , sessionID :: String
  , role :: String
  , time :: { created :: Number, completed :: Maybe Number }
  , error :: Maybe MessageError
  , parentID :: String
  , modelID :: String
  , providerID :: String
  , mode :: String
  , agent :: String
  , path :: { cwd :: String, root :: String }
  , summary :: Maybe Boolean
  , cost :: Number
  , tokens :: StepTokens
  , finish :: Maybe String
  }

data Info
  = InfoUser UserMessage
  | InfoAssistant AssistantMessage

infoId :: Info -> String
infoId = case _ of
  InfoUser u -> u.id
  InfoAssistant a -> a.id

infoSessionId :: Info -> String
infoSessionId = case _ of
  InfoUser u -> u.sessionID
  InfoAssistant a -> a.sessionID

type WithParts =
  { info :: Info
  , parts :: Array Part
  }

-- ════════════════════════════════════════════════════════════════════════════
-- UI TYPES (for LLM conversion)
-- ════════════════════════════════════════════════════════════════════════════

type UIMessage =
  { id :: String
  , role :: String
  , parts :: Array UIPart
  }

data UIPart
  = UIText { text :: String, providerMetadata :: Maybe (Array { key :: String, value :: String }) }
  | UIFile { url :: String, mediaType :: String, filename :: Maybe String }
  | UIToolOutput 
      { toolName :: String
      , state :: String
      , toolCallId :: String
      , input :: Array { key :: String, value :: String }
      , output :: Maybe String
      , errorText :: Maybe String
      }
  | UIReasoning { text :: String }
  | UIStepStart
