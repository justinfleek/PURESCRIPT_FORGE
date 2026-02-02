-- | XTerm FFI Module - Terminal Emulator Bindings
-- |
-- | **What:** Provides FFI bindings for xterm.js terminal emulator library, enabling
-- |         integrated terminal interface in the sidepanel.
-- | **Why:** Enables users to execute shell commands directly from the sidepanel without
-- |         leaving the editor, improving workflow efficiency.
-- | **How:** Uses foreign function imports to create xterm.js terminal instances, handle
-- |         user input/output, and manage terminal lifecycle (create, open, clear, dispose).
-- |
-- | **Dependencies:** None (pure FFI bindings, requires xterm.js JavaScript library)
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.FFI.XTerm as XTerm
-- |
-- | -- Create terminal
-- | terminal <- liftEffect $ XTerm.create
-- |   { rows: 24, cols: 80, cursorBlink: true, fontSize: 14
-- |   , fontFamily: "monospace"
-- |   , theme: { background: "#000000", foreground: "#ffffff"
-- |            , cursor: "#ffffff", selection: "#ffffff" }
-- |   }
-- |
-- | -- Open in DOM element
-- | liftEffect $ XTerm.open terminal "terminal-element-id"
-- |
-- | -- Write output
-- | liftEffect $ XTerm.writeln terminal "Hello, World!"
-- |
-- | -- Handle input
-- | liftEffect $ XTerm.onData terminal \input -> handleInput input
-- | ```
-- |
-- | Based on spec 57-TERMINAL-EMBED.md
module Sidepanel.FFI.XTerm where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, makeAff)
import Data.Either (Either)

-- | Opaque Terminal type
foreign import data Terminal :: Type

-- | Terminal options
type TerminalOptions =
  { rows :: Int
  , cols :: Int
  , cursorBlink :: Boolean
  , fontSize :: Int
  , fontFamily :: String
  , theme :: TerminalTheme
  }

type TerminalTheme =
  { background :: String
  , foreground :: String
  , cursor :: String
  , selection :: String
  }

-- | Create terminal instance
foreign import create :: TerminalOptions -> Effect Terminal

-- | Open terminal in DOM element
foreign import open :: Terminal -> String -> Effect Unit

-- | Write text to terminal
foreign import write :: Terminal -> String -> Effect Unit

-- | Write line to terminal
foreign import writeln :: Terminal -> String -> Effect Unit

-- | Clear terminal
foreign import clear :: Terminal -> Effect Unit

-- | Reset terminal
foreign import reset :: Terminal -> Effect Unit

-- | Set onData callback (user input)
foreign import onData :: Terminal -> (String -> Effect Unit) -> Effect Unit

-- | Set onLineFeed callback
foreign import onLineFeed :: Terminal -> Effect Unit -> Effect Unit

-- | Resize terminal
foreign import resize :: Terminal -> Int -> Int -> Effect Unit

-- | Focus terminal
foreign import focus :: Terminal -> Effect Unit

-- | Blur terminal
foreign import blur :: Terminal -> Effect Unit

-- | Dispose terminal
foreign import dispose :: Terminal -> Effect Unit

-- | Get terminal element ID
foreign import elementId :: Terminal -> Effect String
