-- | Agent Output Viewer FFI
-- | Foreign function interface for clipboard, markdown, etc.
module Nexus.AgentOutputViewer.FFI where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either)

-- | Copy text to clipboard (async)
foreign import copyToClipboard :: String -> Aff (Either String Unit)

-- | Render markdown to HTML
foreign import renderMarkdown :: String -> Aff String

-- | Set innerHTML of element by ref label
foreign import setInnerHTML :: String -> String -> Effect Unit
