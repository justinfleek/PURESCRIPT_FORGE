-- | FFI bindings for Tetris game utilities
module Sidepanel.Components.EasterEggs.Tetris.TetrisFFI
  ( getCurrentTime
  ) where

import Effect (Effect)

-- | Get the current timestamp in milliseconds (Date.now())
foreign import getCurrentTime :: Effect Number
