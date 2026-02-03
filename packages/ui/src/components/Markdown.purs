-- | Markdown Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/markdown.tsx (265 lines)
-- |
-- | Rendered markdown content with syntax highlighting and copy support.
-- | Uses FFI for marked.js parsing and DOMPurify sanitization.
-- | Pure Halogen implementation for component structure.
-- |
-- | Data Attributes:
-- | - `data-component="markdown"` - Root element
-- | - `data-component="markdown-code"` - Code block wrapper
-- | - `data-slot="markdown-copy-button"` - Copy button
-- | - `data-copied` - Present when copy succeeded
-- | - `data-slot="copy-icon"` - Copy icon
-- | - `data-slot="check-icon"` - Check icon (shown after copy)
-- |
-- | Security:
-- | - DOMPurify configuration prevents XSS
-- | - External links get rel="noopener noreferrer"
-- | - Forbidden: style tags, script contents
-- |
-- | Caching:
-- | - LRU cache with max 200 entries
-- | - Key: cacheKey prop or content hash
module UI.Components.Markdown
  ( component
  , Input
  , Slot
  , defaultInput
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Markdown input props
type Input =
  { text :: String            -- Markdown text to render
  , cacheKey :: Maybe String  -- Optional cache key
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { text: ""
  , cacheKey: Nothing
  , className: Nothing
  }

-- | Internal state
type State =
  { input :: Input
  , renderedHtml :: String    -- Sanitized HTML output
  , isLoading :: Boolean
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | RenderComplete String

-- | Slot type for parent components
type Slot id = forall q o. H.Slot q o id

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPONENT
-- ═══════════════════════════════════════════════════════════════════════════════

component :: forall q o m. MonadAff m => H.Component q Input o m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { input
  , renderedHtml: ""
  , isLoading: true
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  -- The actual HTML is rendered via innerHTML in the FFI
  -- This div is a container that will be populated
  HH.div
    ([ HP.attr (HH.AttrName "data-component") "markdown"
    , HP.ref (H.RefLabel "markdown-container")
    ] <> classAttr state.input.className)
    [ if state.isLoading
        then HH.text ""  -- Loading
        else HH.text ""  -- Content is set via FFI
    ]

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action () o m Unit
handleAction = case _ of
  Initialize -> do
    state <- H.get
    renderMarkdown state.input

  Receive newInput -> do
    oldInput <- H.gets _.input
    H.modify_ _ { input = newInput }
    -- Only re-render if text changed
    when (newInput.text /= oldInput.text) do
      renderMarkdown newInput

  RenderComplete html -> do
    H.modify_ _ { renderedHtml = html, isLoading = false }
    -- Apply HTML to container via ref
    mContainer <- H.getHTMLElementRef (H.RefLabel "markdown-container")
    case mContainer of
      Nothing -> pure unit
      Just container -> do
        liftEffect $ setInnerHtml container html
        liftEffect $ setupCodeCopy container

-- | Render markdown text to HTML
renderMarkdown :: forall o m. MonadAff m => Input -> H.HalogenM State Action () o m Unit
renderMarkdown input = do
  H.modify_ _ { isLoading = true }
  
  -- Check cache first
  mCached <- liftEffect $ getCached (getCacheKey input)
  case mCached of
    Just html -> do
      handleAction (RenderComplete html)
    Nothing -> do
      -- Parse markdown
      html <- liftAff $ parseMarkdown input.text
      -- Sanitize
      safeHtml <- liftEffect $ sanitize html
      -- Cache result
      liftEffect $ setCached (getCacheKey input) safeHtml
      handleAction (RenderComplete safeHtml)

-- | Get cache key from input
getCacheKey :: Input -> String
getCacheKey input = case input.cacheKey of
  Just key -> key
  Nothing -> input.text  -- Use text as key (will be hashed in FFI)

-- ═══════════════════════════════════════════════════════════════════════════════
-- FFI
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parse markdown to HTML using marked.js
foreign import parseMarkdown :: String -> Aff String

-- | Sanitize HTML using DOMPurify
foreign import sanitize :: String -> Effect String

-- | Get cached HTML
foreign import getCached :: String -> Effect (Maybe String)

-- | Set cached HTML
foreign import setCached :: String -> String -> Effect Unit

-- | Set innerHTML on element
foreign import setInnerHtml :: forall element. element -> String -> Effect Unit

-- | Setup code block copy buttons
foreign import setupCodeCopy :: forall element. element -> Effect Unit
