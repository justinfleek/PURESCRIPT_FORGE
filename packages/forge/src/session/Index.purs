-- | Session Index - main entry point
-- | 1:1 parity with opencode-dev/packages/opencode/src/session/index.ts
module Forge.Session.Index
  ( module Forge.Session.Session
  , module Forge.Session.Compaction
  , module Forge.Session.LLM
  , module Forge.Session.Processor
  , module Forge.Session.Prompt
  ) where

-- Re-export all session modules
import Forge.Session.Session (SessionInfo, create, fork, get, list, remove, update, touch, messages, updateMessage, updatePart, removePart, removeMessage, getUsage, initialize, Event)
import Forge.Session.Compaction (CompactionConfig, CompactionResult, compact, needsCompaction)
import Forge.Session.LLM (StreamInput, stream)
import Forge.Session.Processor (Info, Result, create) as Processor
import Forge.Session.Prompt (PromptRequest, PromptResult, sendPrompt, cancelPrompt)
