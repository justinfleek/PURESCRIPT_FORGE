-- | TUI Event handling
module Forge.CLI.Cmd.TUI.Event where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe)

-- | TUI Event types
data TUIEvent
  = KeyPress String
  | Resize Int Int
  | Focus Boolean
  | Paste String
  | Mouse MouseEvent

type MouseEvent =
  { x :: Int
  , y :: Int
  , button :: Int
  }

-- | Event handler type
type EventHandler = TUIEvent -> Effect Unit

-- | FFI imports
foreign import subscribeKeyImpl :: (String -> Effect Unit) -> Effect Unit
foreign import subscribeResizeImpl :: (Int -> Int -> Effect Unit) -> Effect Unit
foreign import unsubscribeImpl :: Effect Unit

-- | Subscribe to TUI events
subscribe :: EventHandler -> Effect Unit
subscribe handler = do
  subscribeKeyImpl (\key -> handler (KeyPress key))
  subscribeResizeImpl (\w h -> handler (Resize w h))

-- | Unsubscribe from TUI events
unsubscribe :: Effect Unit
unsubscribe = unsubscribeImpl
