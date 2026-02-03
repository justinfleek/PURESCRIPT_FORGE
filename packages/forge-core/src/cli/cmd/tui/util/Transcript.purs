-- | TUI Transcript utilities
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/tui/util/transcript.ts
module Forge.CLI.Cmd.TUI.Util.Transcript where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Transcript entry
type TranscriptEntry =
  { role :: String
  , content :: String
  , timestamp :: Number
  }

-- | Export transcript to file
exportTranscript :: Array TranscriptEntry -> String -> Aff (Either String Unit)
exportTranscript entries path = notImplemented "CLI.Cmd.TUI.Util.Transcript.exportTranscript"

-- | Format transcript for display
formatTranscript :: Array TranscriptEntry -> String
formatTranscript entries = "" -- TODO: Implement
