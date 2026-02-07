-- | Rate Limit Indicator Component - Display Venice API Rate Limits
-- |
-- | **What:** Displays current Venice API rate limit status (requests/min, tokens/min)
-- |         with visual gauges and reset countdown timers. Shows warnings when limits
-- |         are approached or exceeded.
-- | **Why:** Provides users with visibility into rate limit status, helping them
-- |         understand when they may be throttled and when limits reset.
-- | **How:** Renders progress bars for request and token limits, calculates reset
-- |         times, and displays backoff status when rate limited.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.RateLimit`: Rate limit state types
-- | - `Sidepanel.Utils.Time`: Time formatting utilities
-- | - `Sidepanel.Utils.Currency`: Number formatting utilities
-- |
-- | **Mathematical Foundation:**
-- | - **Gauge Percentage:** `(remaining / limit) * 100` for visual progress
-- | - **Reset Time:** Calculated from `resetTime - currentTime`
-- | - **Warning Thresholds:** < 20% remaining = warning, < 5% = critical
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.RateLimitIndicator as RateLimitIndicator
-- |
-- | -- In parent component:
-- | HH.slot _rateLimit unit RateLimitIndicator.component
-- |   { rateLimitState: appState.rateLimit, currentTime: now }
-- |   (const HandleAppAction)
-- | ```
-- |
-- | Based on spec 14-RATE-LIMIT-HANDLING.md
module Sidepanel.Components.RateLimitIndicator where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Effect.Aff (Aff, delay, Milliseconds(..))
import Data.Maybe (Maybe(..))
import Sidepanel.State.RateLimit (RateLimitState, getTimeUntilReset, isRateLimited)
import Sidepanel.Utils.Time (formatDuration)
import Sidepanel.Utils.Currency (formatNumber)
import Sidepanel.FFI.DateTime (getCurrentDateTime)
import Data.DateTime (DateTime)

-- | Component input
type Input =
  { rateLimitState :: RateLimitState
  , currentTime :: DateTime
  }

-- | Component state
type State =
  { rateLimitState :: RateLimitState
  , currentTime :: DateTime
  }

-- | Actions
data Action
  = Receive Input
  | Initialize
  | UpdateCurrentTime DateTime
  | Tick  -- Update timer every second

-- | Outputs
data Output
  = RateLimitWarning String  -- Warning message when limits approached

-- | Component
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \input ->
      { rateLimitState: input.rateLimitState
      , currentTime: input.currentTime
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      , initialize = Just Initialize
      }
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "rate-limit-indicator") ]
    [ HH.div
        [ HP.class_ (H.ClassName "section-title") ]
        [ HH.text "Rate Limits" ]
    , renderGauge
        "Requests"
        state.rateLimitState.requestsRemaining
        state.rateLimitState.requestLimit
        (getTimeUntilReset state.rateLimitState state.currentTime)
        state.rateLimitState.requestResetTime
    , renderGauge
        "Tokens"
        state.rateLimitState.tokensRemaining
        state.rateLimitState.tokenLimit
        (getTimeUntilReset state.rateLimitState state.currentTime)
        state.rateLimitState.tokenResetTime
    , if isRateLimited state.rateLimitState then
        renderWarning state.rateLimitState.backoffMs
      else
        HH.text ""
    ]

renderGauge :: forall m. String -> Int -> Int -> Int -> Maybe DateTime -> H.ComponentHTML Action () m
renderGauge label remaining total resetMs resetTime =
  let
    percent = (Int.toNumber remaining / Int.toNumber total) * 100.0
    barClass = if percent < 5.0 then "gauge--critical"
               else if percent < 20.0 then "gauge--warning"
               else ""
    resetText = if resetMs > 0
      then "resets in " <> formatResetTime resetMs
      else "reset"
  in
    HH.div
      [ HP.class_ (H.ClassName "rate-gauge") ]
      [ HH.div
          [ HP.class_ (H.ClassName "rate-gauge__label") ]
          [ HH.text label ]
      , HH.div
          [ HP.classes [ H.ClassName "rate-gauge__bar", H.ClassName barClass ] ]
          [ HH.div
              [ HP.class_ (H.ClassName "rate-gauge__fill")
              , HP.style $ "width: " <> show percent <> "%"
              ]
              []
          ]
      , HH.div
          [ HP.class_ (H.ClassName "rate-gauge__value") ]
          [ HH.text $ formatNumber remaining <> "/" <> formatNumber total ]
      , HH.div
          [ HP.class_ (H.ClassName "rate-gauge__reset") ]
          [ HH.text $ "(" <> resetText <> ")" ]
      ]

renderWarning :: forall m. Number -> H.ComponentHTML Action () m
renderWarning backoffMs =
  let
    backoffSeconds = round (backoffMs / 1000.0)
  in
    HH.div
      [ HP.class_ (H.ClassName "rate-limit-warning") ]
      [ HH.text $ "⚠ Rate limited - retrying in " <> show backoffSeconds <> "s" ]

formatResetTime :: Int -> String
formatResetTime ms =
  let
    seconds = ms / 1000
    minutes = seconds / 60
    hours = minutes / 60
  in
    if hours > 0 then
      show hours <> "h " <> show (minutes `mod` 60) <> "m"
    else if minutes > 0 then
      show minutes <> "m " <> show (seconds `mod` 60) <> "s"
    else
      show seconds <> "s"

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Start ticker to update current time every second
    void $ H.fork $ startTicker
  
  Receive input -> do
    H.modify_ _
      { rateLimitState = input.rateLimitState
      , currentTime = input.currentTime
      }
  
  UpdateCurrentTime dt ->
    H.modify_ _ { currentTime = dt }
  
  Tick -> do
    currentTime <- liftEffect getCurrentDateTime
    H.modify_ _ { currentTime = currentTime }
    -- Check if rate limited and emit warning if needed
    state <- H.get
    if isRateLimited state.rateLimitState then
      H.raise (RateLimitWarning "Rate limit active")
    else
      pure unit

-- | Start ticker - Update current time every second
startTicker :: forall m. MonadAff m => H.HalogenM State Action () Output m Unit
startTicker = do
  delay (Milliseconds 1000.0)
  handleAction Tick
  startTicker  -- Recursive - keep ticking
