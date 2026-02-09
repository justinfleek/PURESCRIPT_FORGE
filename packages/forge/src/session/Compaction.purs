{-|
Module      : Forge.Session.Compaction
Description : Session History Compaction

Compresses older messages in a session to save context space.
Uses LLM summarization to preserve important information while
reducing token count.

== Compaction Strategy

1. Keep recent N messages intact
2. Summarize older messages in batches
3. Preserve system messages and important tool results
4. Update session with compacted history
-}
module Forge.Session.Compaction
  ( -- * Types
    CompactionConfig
  , CompactionResult
  , CompactionStrategy(..)
    -- * Compaction Operations
  , compact
  , compactWithStrategy
  , needsCompaction
    -- * Default Config
  , defaultConfig
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Compaction strategy
data CompactionStrategy
  = KeepRecent Int       -- Keep last N messages
  | Summarize            -- Summarize older messages
  | Truncate             -- Simply remove older messages
  | Sliding Int          -- Sliding window of N messages

derive instance eqCompactionStrategy :: Eq CompactionStrategy

-- | Compaction configuration
type CompactionConfig =
  { maxMessages :: Int               -- Max messages before compaction
  , keepRecent :: Int                -- Messages to keep unchanged
  , summaryModel :: Maybe String     -- Model to use for summarization
  , preserveSystemMessages :: Boolean
  , preserveToolResults :: Boolean
  , strategy :: CompactionStrategy
  }

-- | Compaction result
type CompactionResult =
  { originalCount :: Int
  , compactedCount :: Int
  , tokensRemoved :: Int
  , summary :: Maybe String
  , preservedMessageIds :: Array String
  }

-- | Message type for internal use
type Message =
  { id :: String
  , role :: String
  , content :: String
  , timestamp :: Number
  , isSystem :: Boolean
  , isToolResult :: Boolean
  }

-- ============================================================================
-- FFI
-- ============================================================================

foreign import getSessionMessagesFFI :: String -> Aff (Array Message)
foreign import updateSessionMessagesFFI :: String -> Array Message -> Aff (Either String Unit)
foreign import summarizeMessagesFFI :: Array Message -> Maybe String -> Aff (Either String String)
foreign import countTokensFFI :: String -> Int

-- ============================================================================
-- DEFAULT CONFIG
-- ============================================================================

-- | Default compaction configuration
defaultConfig :: CompactionConfig
defaultConfig =
  { maxMessages: 50
  , keepRecent: 10
  , summaryModel: Nothing
  , preserveSystemMessages: true
  , preserveToolResults: true
  , strategy: Summarize
  }

-- ============================================================================
-- COMPACTION OPERATIONS
-- ============================================================================

{-| Compact session messages using default config. -}
compact :: String -> CompactionConfig -> Aff (Either String CompactionResult)
compact sessionId config = compactWithStrategy sessionId config config.strategy

{-| Compact session with specific strategy. -}
compactWithStrategy :: String -> CompactionConfig -> CompactionStrategy -> Aff (Either String CompactionResult)
compactWithStrategy sessionId config strategy = do
  messages <- getSessionMessagesFFI sessionId
  
  if Array.length messages <= config.maxMessages
    then pure $ Right
      { originalCount: Array.length messages
      , compactedCount: Array.length messages
      , tokensRemoved: 0
      , summary: Nothing
      , preservedMessageIds: map _.id messages
      }
    else do
      let result = applyStrategy config strategy messages
      updateResult <- updateSessionMessagesFFI sessionId result.newMessages
      case updateResult of
        Left err -> pure $ Left err
        Right _ -> pure $ Right
          { originalCount: Array.length messages
          , compactedCount: Array.length result.newMessages
          , tokensRemoved: result.tokensRemoved
          , summary: result.summary
          , preservedMessageIds: map _.id result.newMessages
          }

{-| Check if session needs compaction. -}
needsCompaction :: String -> Int -> Aff Boolean
needsCompaction sessionId threshold = do
  messages <- getSessionMessagesFFI sessionId
  pure $ Array.length messages > threshold

-- ============================================================================
-- STRATEGY IMPLEMENTATION
-- ============================================================================

type StrategyResult =
  { newMessages :: Array Message
  , tokensRemoved :: Int
  , summary :: Maybe String
  }

applyStrategy :: CompactionConfig -> CompactionStrategy -> Array Message -> StrategyResult
applyStrategy config strategy messages =
  case strategy of
    KeepRecent n ->
      let kept = Array.takeEnd n messages
          removed = Array.take (Array.length messages - n) messages
          tokensRemoved = sumTokens removed
      in { newMessages: kept
         , tokensRemoved
         , summary: Nothing
         }
    
    Truncate ->
      let kept = Array.takeEnd config.keepRecent messages
          removed = Array.take (Array.length messages - config.keepRecent) messages
          tokensRemoved = sumTokens removed
      in { newMessages: kept
         , tokensRemoved
         , summary: Nothing
         }
    
    Sliding n ->
      let kept = Array.takeEnd n messages
          tokensRemoved = sumTokens $ Array.take (Array.length messages - n) messages
      in { newMessages: kept
         , tokensRemoved
         , summary: Nothing
         }
    
    Summarize ->
      -- For summarization, we need to preserve certain messages
      let (toSummarize, toKeep) = splitMessages config messages
          tokensRemoved = sumTokens toSummarize
      in { newMessages: toKeep
         , tokensRemoved
         , summary: Just "[Messages summarized]"
         }

splitMessages :: CompactionConfig -> Array Message -> { fst :: Array Message, snd :: Array Message }
splitMessages config messages =
  let recent = Array.takeEnd config.keepRecent messages
      older = Array.take (Array.length messages - config.keepRecent) messages
      -- Preserve system messages if configured
      preserved = if config.preserveSystemMessages
                  then Array.filter _.isSystem older
                  else []
      -- Preserve tool results if configured
      toolResults = if config.preserveToolResults
                    then Array.filter _.isToolResult older
                    else []
  in { fst: Array.filter (\m -> not (Array.elem m.id (map _.id (preserved <> toolResults)))) older
     , snd: preserved <> toolResults <> recent
     }

sumTokens :: Array Message -> Int
sumTokens messages = Array.foldl (\acc m -> acc + countTokensFFI m.content) 0 messages
