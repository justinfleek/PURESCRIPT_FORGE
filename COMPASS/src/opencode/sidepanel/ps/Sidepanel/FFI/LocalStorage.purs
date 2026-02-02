-- | LocalStorage FFI Module - Browser LocalStorage Interface
-- |
-- | **What:** Provides type-safe PureScript bindings to browser localStorage API for
-- |         persistent key-value storage in the browser.
-- | **Why:** Enables persistent storage of application settings, preferences, and cached
-- |         data across browser sessions. Essential for user preferences and offline support.
-- | **How:** Uses foreign function imports to wrap JavaScript localStorage API, providing
-- |         PureScript-friendly types (Maybe String for getItem, Effect for side effects).
-- |
-- | **Dependencies:** None (pure FFI bindings)
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.FFI.LocalStorage as LocalStorage
-- |
-- | -- Get value
-- | value <- liftEffect $ LocalStorage.getItem "key"
-- | -- value :: Maybe String
-- |
-- | -- Set value
-- | liftEffect $ LocalStorage.setItem "key" "value"
-- |
-- | -- Remove value
-- | liftEffect $ LocalStorage.removeItem "key"
-- | ```
module Sidepanel.FFI.LocalStorage where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe)

-- | Get value from localStorage
foreign import getItem :: String -> Effect (Maybe String)

-- | Set value in localStorage
foreign import setItem :: String -> String -> Effect Unit

-- | Remove value from localStorage
foreign import removeItem :: String -> Effect Unit

-- | Clear all localStorage
foreign import clear :: Effect Unit

-- | Get all keys from localStorage
foreign import getAllKeys :: Effect (Array String)
