-- | TUI Terminal utilities
module Forge.CLI.Cmd.TUI.Util.Terminal where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe(..))

-- | Terminal size
type TerminalSize =
  { width :: Int
  , height :: Int
  }

-- | FFI imports
foreign import getWidthImpl :: Effect Int
foreign import getHeightImpl :: Effect Int
foreign import isTTYImpl :: Effect Boolean
foreign import enableRawModeImpl :: Effect Unit
foreign import disableRawModeImpl :: Effect Unit
foreign import clearImpl :: Effect Unit
foreign import moveCursorImpl :: Int -> Int -> Effect Unit

-- | Get terminal size
getSize :: Effect (Maybe TerminalSize)
getSize = do
  w <- getWidthImpl
  h <- getHeightImpl
  pure $ Just { width: w, height: h }

-- | Check if running in a TTY
isTTY :: Effect Boolean
isTTY = isTTYImpl

-- | Enable raw mode
enableRawMode :: Effect Unit
enableRawMode = enableRawModeImpl

-- | Disable raw mode
disableRawMode :: Effect Unit
disableRawMode = disableRawModeImpl

-- | Clear the terminal
clear :: Effect Unit
clear = clearImpl

-- | Move cursor to position
moveCursor :: Int -> Int -> Effect Unit
moveCursor = moveCursorImpl
