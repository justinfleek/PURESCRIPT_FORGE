-- | Typewriter Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/typewriter.tsx (56 lines)
-- |
-- | Animated text typing effect with blinking cursor.
-- | Uses Halogen subscriptions for animation timing.
-- |
-- | Animation Details:
-- | - 5% chance: 150-250ms (long pause)
-- | - 10% chance: 80-140ms (medium pause)
-- | - 85% chance: 30-80ms (normal typing)
-- | - Initial delay: 200ms before typing starts
-- | - Cursor blinks for 2 seconds after typing, then fades
-- |
-- | Data Attributes:
-- | - No specific data attributes
-- | - Uses CSS class `blinking-cursor` for cursor animation
module UI.Components.Typewriter
  ( component
  , Input
  , Slot
  , defaultInput
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.String as String
import Effect (Effect)
import Effect.Aff (Milliseconds(..), delay)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (liftEffect)
import Effect.Random (random)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Element type for the wrapper
data ElementType
  = P
  | H1
  | H2
  | H3
  | Span
  | Div

derive instance eqElementType :: Eq ElementType

stringToElementType :: String -> ElementType
stringToElementType "p" = P
stringToElementType "h1" = H1
stringToElementType "h2" = H2
stringToElementType "h3" = H3
stringToElementType "span" = Span
stringToElementType "div" = Div
stringToElementType _ = P

-- | Typewriter input props
type Input =
  { text :: String          -- Text to type out
  , elementType :: String   -- HTML element type ("p", "h1", etc.)
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { text: ""
  , elementType: "p"
  , className: Nothing
  }

-- | Internal state
type State =
  { input :: Input
  , displayed :: String     -- Currently displayed text
  , typing :: Boolean       -- Currently typing
  , showCursor :: Boolean   -- Show cursor
  , charIndex :: Int        -- Current character index
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | TypeNextChar
  | HideCursor

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
  , displayed: ""
  , typing: false
  , showCursor: true
  , charIndex: 0
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  let
    elemType = stringToElementType state.input.elementType
    elemName = case elemType of
      P -> "p"
      H1 -> "h1"
      H2 -> "h2"
      H3 -> "h3"
      Span -> "span"
      Div -> "div"
  in
    HH.element (HH.ElemName elemName)
      (classAttr state.input.className)
      [ HH.text state.displayed
      , if state.showCursor
          then renderCursor state.typing
          else HH.text ""
      ]

renderCursor :: forall w i. Boolean -> HH.HTML w i
renderCursor typing =
  HH.span
    [ HP.class_ (HH.ClassName (if typing then "" else "blinking-cursor")) ]
    [ HH.text "│" ]

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
    when (state.input.text /= "") do
      H.modify_ _ { typing = true, showCursor = true, displayed = "", charIndex = 0 }
      -- Initial delay before typing starts
      liftAff $ delay (Milliseconds 200.0)
      handleAction TypeNextChar

  Receive newInput -> do
    oldInput <- H.gets _.input
    when (newInput.text /= oldInput.text) do
      H.modify_ _ 
        { input = newInput
        , typing = true
        , showCursor = true
        , displayed = ""
        , charIndex = 0
        }
      liftAff $ delay (Milliseconds 200.0)
      handleAction TypeNextChar
    H.modify_ _ { input = newInput }

  TypeNextChar -> do
    state <- H.get
    let textLength = String.length state.input.text
    if state.charIndex < textLength
      then do
        -- Type next character
        let newDisplayed = String.take (state.charIndex + 1) state.input.text
        H.modify_ _ { displayed = newDisplayed, charIndex = state.charIndex + 1 }
        -- Get random delay
        delayMs <- liftEffect getTypingDelay
        liftAff $ delay (Milliseconds delayMs)
        handleAction TypeNextChar
      else do
        -- Typing complete
        H.modify_ _ { typing = false }
        -- Hide cursor after 2 seconds
        liftAff $ delay (Milliseconds 2000.0)
        handleAction HideCursor

  HideCursor -> do
    H.modify_ _ { showCursor = false }

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPING DELAY
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get a random typing delay in milliseconds
-- | Uses the pattern from original:
-- | - 5% chance: 150-250ms (long pause)
-- | - 10% chance: 80-140ms (medium pause)
-- | - 85% chance: 30-80ms (normal typing)
getTypingDelay :: Effect Number
getTypingDelay = do
  r <- random
  pure $ if r < 0.05
    then 150.0 + r * 100.0      -- Long pause: 150-250ms
    else if r < 0.15
      then 80.0 + r * 60.0      -- Medium pause: 80-140ms
      else 30.0 + r * 50.0      -- Normal typing: 30-80ms

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses:
-- - Effect.Random for random delays
-- - Effect.Aff.delay for timing
-- All are standard PureScript libraries.
