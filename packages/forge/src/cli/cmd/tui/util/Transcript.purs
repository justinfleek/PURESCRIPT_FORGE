-- | TUI Transcript utilities
-- | Ported from COMPASS reference: opencode/cli/cmd/tui/util/Transcript.purs
module Forge.CLI.Cmd.TUI.Util.Transcript where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.String as String
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

-- | Transcript entry
type TranscriptEntry =
  { role :: String
  , content :: String
  , timestamp :: Number
  }

-- | Export transcript to file
exportTranscript :: Array TranscriptEntry -> String -> Aff (Either String Unit)
exportTranscript entries filePath =
  let formatted = formatTranscriptFull entries
  in fromEffectFnAff (writeTranscriptFFI filePath formatted)

-- | Format transcript for display
-- | Formats each entry as "[role] content" with newline separation
formatTranscript :: Array TranscriptEntry -> String
formatTranscript entries =
  String.joinWith "\n\n" (Array.map formatEntry entries)
  where
    formatEntry entry = "[" <> entry.role <> "] " <> entry.content

-- | Format transcript with timestamps for export
formatTranscriptFull :: Array TranscriptEntry -> String
formatTranscriptFull entries =
  String.joinWith "\n\n---\n\n" (Array.map formatEntryFull entries)
  where
    formatEntryFull entry =
      "[" <> entry.role <> "] (t=" <> show entry.timestamp <> ")\n" <> entry.content

-- | FFI: Write transcript to file
foreign import writeTranscriptFFI :: String -> String -> EffectFnAff (Either String Unit)
