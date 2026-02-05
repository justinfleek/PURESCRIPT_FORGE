-- | DOM Manipulation FFI Module - DOM and CSS Injection
-- |
-- | **What:** Provides FFI bindings for DOM manipulation, specifically CSS injection for
-- |         theme application and style element management.
-- | **Why:** Enables dynamic theme application (PRISM themes) by injecting CSS into the
-- |         document. Essential for theme switching and dynamic styling.
-- | **How:** Uses foreign function imports to manipulate DOM (inject CSS into head, ensure
-- |         theme style element exists). Typically creates or updates a `<style>` element
-- |         in the document head.
-- |
-- | **Dependencies:** None (pure FFI bindings)
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.FFI.DOM as DOM
-- |
-- | -- Inject CSS
-- | liftEffect $ DOM.injectCSS cssString
-- |
-- | -- Ensure theme style element exists
-- | liftEffect DOM.ensureThemeStyleElement
-- | ```
module Sidepanel.FFI.DOM where

import Prelude
import Effect (Effect)

-- | Inject CSS into document head
foreign import injectCSS :: String -> Effect Unit

-- | Inject CSS with specific ID (for theme management)
foreign import injectCSSWithId :: String -> String -> Effect Unit

-- | Get or create style element for theme
foreign import ensureThemeStyleElement :: Effect Unit

-- | Set CSS custom property (variable) on document root
foreign import setCSSVariable :: String -> String -> Effect Unit
