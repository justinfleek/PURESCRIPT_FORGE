-- | SessionTurn Status Module
-- | Status computation logic for session turns.
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/session-turn.tsx

module UI.Components.SessionTurn.Status
  ( computeStatusFromPart
  , formatDuration
  , extractBoldTopic
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.Regex (regex, match)
import Data.String.Regex.Flags (noFlags)
import Data.Either (hush)
import Data.Array (head, (!!))
import UI.Components.MessagePart.Types (Part(..), ToolPartData)

-- ═══════════════════════════════════════════════════════════════════════════════
-- STATUS COMPUTATION
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Compute status text from the current part
computeStatusFromPart :: Maybe Part -> Maybe String
computeStatusFromPart Nothing = Nothing
computeStatusFromPart (Just part) = case part of
  ToolPart tp -> computeToolStatus tp.tool
  ReasoningPart rp -> computeReasoningStatus rp.text
  TextPart _ -> Just "Gathering thoughts..."
  _ -> Nothing

-- | Get status for tool execution
computeToolStatus :: String -> Maybe String
computeToolStatus tool = case tool of
  "task" -> Just "Delegating to agent..."
  "todowrite" -> Just "Planning..."
  "todoread" -> Just "Planning..."
  "read" -> Just "Gathering context..."
  "list" -> Just "Searching codebase..."
  "grep" -> Just "Searching codebase..."
  "glob" -> Just "Searching codebase..."
  "webfetch" -> Just "Searching web..."
  "edit" -> Just "Making edits..."
  "write" -> Just "Making edits..."
  "bash" -> Just "Running commands..."
  _ -> Nothing

-- | Get status for reasoning part
computeReasoningStatus :: String -> Maybe String
computeReasoningStatus text =
  case extractBoldTopic text of
    Just topic -> Just ("Thinking about " <> topic <> "...")
    Nothing -> Just "Thinking..."

-- | Extract bold topic from reasoning text (e.g., "**Topic**" -> "Topic")
extractBoldTopic :: String -> Maybe String
extractBoldTopic text =
  let trimmed = String.trim text
      -- Match **...** at start of text
      pattern = hush $ regex "^\\*\\*(.+?)\\*\\*" noFlags
  in case pattern of
    Nothing -> Nothing
    Just re -> case match re trimmed of
      Nothing -> Nothing
      Just matches -> do
        -- Get capture group 1
        m <- matches !! 1
        m

-- ═══════════════════════════════════════════════════════════════════════════════
-- DURATION FORMATTING
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Format duration between two timestamps
formatDuration :: Number -> Number -> String
formatDuration from to =
  let seconds = (to - from) / 1000.0
      minutes = seconds / 60.0
  in if seconds < 60.0
     then formatSeconds seconds
     else formatMinutesSeconds minutes seconds

formatSeconds :: Number -> String
formatSeconds s =
  let rounded = floor s
  in show rounded <> "s"

formatMinutesSeconds :: Number -> Number -> String
formatMinutesSeconds m s =
  let mins = floor m
      secs = floor (s - (toNumber mins * 60.0))
  in show mins <> "m " <> show secs <> "s"

-- Helpers
floor :: Number -> Int
floor n = unsafeFloor n

toNumber :: Int -> Number
toNumber = unsafeToNumber

foreign import unsafeFloor :: Number -> Int
foreign import unsafeToNumber :: Int -> Number
