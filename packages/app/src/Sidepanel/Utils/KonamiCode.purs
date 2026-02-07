-- | Konami Code Detection Utility
-- |
-- | **What:** Detects the classic Konami code sequence (Up Up Down Down Left Right Left Right B A)
-- |         and triggers a callback when the sequence is entered.
-- | **Why:** Universal easter egg trigger - classic way to unlock hidden features in games/apps.
-- | **How:** Tracks key sequence and matches against Konami code pattern. Resets on mismatch.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Utils.KonamiCode as KonamiCode
-- |
-- | -- Create detector
-- | detector <- KonamiCode.createDetector \_ -> do
-- |   -- Unlock games!
-- |   H.raise GamesUnlocked
-- |
-- | -- Cleanup when done
-- | KonamiCode.destroyDetector detector
-- | ```
module Sidepanel.Utils.KonamiCode where

import Prelude
import Effect (Effect)
import Data.Array as Array
import Web.UIEvent.KeyboardEvent (KeyboardEvent, key)

-- | Key code type
data KeyCode
  = ArrowUp
  | ArrowDown
  | ArrowLeft
  | ArrowRight
  | KeyB
  | KeyA
  | Other String

derive instance eqKeyCode :: Eq KeyCode

-- | Konami code sequence: Up Up Down Down Left Right Left Right B A
konamiSequence :: Array KeyCode
konamiSequence =
  [ ArrowUp
  , ArrowUp
  , ArrowDown
  , ArrowDown
  , ArrowLeft
  , ArrowRight
  , ArrowLeft
  , ArrowRight
  , KeyB
  , KeyA
  ]

-- | Detector state
type DetectorState =
  { sequence :: Array KeyCode
  , callback :: Effect Unit
  }

-- | Create Konami code detector
foreign import createDetector :: (Effect Unit) -> Effect DetectorState

-- | Destroy detector (cleanup)
foreign import destroyDetector :: DetectorState -> Effect Unit

-- | Parse keyboard event to key code
parseKeyCode :: KeyboardEvent -> KeyCode
parseKeyCode event = case key event of
  "ArrowUp" -> ArrowUp
  "ArrowDown" -> ArrowDown
  "ArrowLeft" -> ArrowLeft
  "ArrowRight" -> ArrowRight
  "b" -> KeyB
  "B" -> KeyB
  "a" -> KeyA
  "A" -> KeyA
  _ -> Other (key event)

-- | Check if sequence matches Konami code
matchesKonamiCode :: Array KeyCode -> Boolean
matchesKonamiCode sequence =
  Array.length sequence >= Array.length konamiSequence &&
  Array.take (Array.length konamiSequence) sequence == konamiSequence

-- | Process key event and check for Konami code match
processKey :: DetectorState -> KeyboardEvent -> Effect Boolean
processKey detector event = do
  let keyCode = parseKeyCode event
  let newSequence = Array.snoc detector.sequence keyCode
  
  -- Check if we have a match
  if matchesKonamiCode newSequence then do
    detector.callback
    pure true
  else
    -- Check if sequence is still valid (prefix of Konami code)
    let prefix = Array.take (Array.length newSequence) konamiSequence
    if newSequence == prefix then
      pure false  -- Still matching, keep going
    else
      pure false  -- Mismatch, reset handled by caller
