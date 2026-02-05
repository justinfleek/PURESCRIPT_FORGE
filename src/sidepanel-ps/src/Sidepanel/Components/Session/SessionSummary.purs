-- | Session Summary Component - Compact Session Display for Dashboard
-- |
-- | **What:** Displays a compact summary of the current active session, including
-- |         model, token counts, and cost. Designed for dashboard integration.
-- | **Why:** Provides quick at-a-glance session information without the full detail
-- |         view of SessionPanel. Optimized for dashboard space constraints.
-- | **How:** Renders session information in a compact card format with key metrics
-- |         displayed prominently.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.AppState`: SessionState type
-- | - `Sidepanel.Utils.Currency`: Currency formatting
-- | - `Sidepanel.Utils.Time`: Time formatting
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.Session.SessionSummary as SessionSummary
-- |
-- | -- In parent component:
-- | HH.slot_ _sessionSummary unit SessionSummary.component
-- |   { session: Just sessionState }
-- | ```
-- |
-- | Based on spec 50-DASHBOARD-LAYOUT.md
module Sidepanel.Components.Session.SessionSummary where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Data.Maybe (Maybe(..))
import Sidepanel.State.AppState (SessionState)
import Sidepanel.Utils.Currency (formatUSD)
import Sidepanel.Utils.Time (formatDuration)
import Sidepanel.FFI.DateTime (getCurrentDateTime)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (liftEffect)
import Effect.Aff (Milliseconds(..), delay, forever, forkAff, killFiber, error)
import Halogen as H

-- | Component input
type Input =
  { session :: Maybe SessionState
  }

-- | Component state
type State =
  { session :: Maybe SessionState
  , duration :: String
  }

-- | Component query
data Query a = UpdateSession (Maybe SessionState) a

-- | Session Summary component
component :: forall m. MonadAff m => H.Component Query Input Void m
component = H.mkComponent
  { initialState: \input ->
      { session: input.session
      , duration: ""
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , initialize = Just Initialize
      }
  }

data Action 
  = Initialize 
  | UpdateDuration

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Void m Unit
handleAction = case _ of
  Initialize -> do
    -- Calculate initial duration if session exists
    state <- H.get
    case state.session of
      Just session -> do
        now <- liftEffect getCurrentDateTime
        let durationStr = formatDuration session.startedAt now
        H.modify_ _ { duration = durationStr }
        
        -- Start ticker to update duration every second
        void $ H.subscribe durationTickerEmitter
      Nothing ->
        pure unit
  
  UpdateDuration -> do
    state <- H.get
    case state.session of
      Just session -> do
        now <- liftEffect getCurrentDateTime
        let durationStr = formatDuration session.startedAt now
        H.modify_ _ { duration = durationStr }
      Nothing ->
        pure unit

-- | Ticker that fires every second to update duration
durationTickerEmitter :: forall m. MonadAff m => H.Emitter m Action
durationTickerEmitter = H.Emitter \emit -> do
  fiber <- forkAff $ forever do
    delay (Milliseconds 1000.0)
    liftEffect $ emit UpdateDuration
  pure $ killFiber (error "unsubscribed") fiber

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Void m (Maybe a)
handleQuery = case _ of
  UpdateSession session k -> do
    -- Update session
    H.modify_ _ { session = session }
    
    -- Update duration if session exists, and start ticker if needed
    case session of
      Just s -> do
        now <- liftEffect getCurrentDateTime
        let durationStr = formatDuration s.startedAt now
        H.modify_ _ { duration = durationStr }
        -- Ticker will continue running (it checks for session in UpdateDuration)
      Nothing ->
        H.modify_ _ { duration = "" }
    
    pure (Just k)

-- | Render session summary
render :: forall m. State -> H.ComponentHTML Action () m
render state = case state.session of
  Nothing ->
    HH.div
      [ HP.class_ (H.ClassName "session-summary") ]
      [ HH.h3_ [ HH.text "Current Session" ]
      , HH.p
          [ HP.class_ (H.ClassName "session-summary__empty") ]
          [ HH.text "No active session" ]
      ]
  
  Just session ->
    HH.div
      [ HP.class_ (H.ClassName "session-summary") ]
      [ HH.h3_ [ HH.text "Current Session" ]
      , HH.div
          [ HP.class_ (H.ClassName "session-summary__content") ]
          [ HH.div
              [ HP.class_ (H.ClassName "session-summary__row") ]
              [ HH.span
                  [ HP.class_ (H.ClassName "session-summary__label") ]
                  [ HH.text "Model:" ]
              , HH.span
                  [ HP.class_ (H.ClassName "session-summary__value") ]
                  [ HH.text session.model ]
              ]
          , HH.div
              [ HP.class_ (H.ClassName "session-summary__row") ]
              [ HH.span
                  [ HP.class_ (H.ClassName "session-summary__label") ]
                  [ HH.text "Messages:" ]
              , HH.span
                  [ HP.class_ (H.ClassName "session-summary__value") ]
                  [ HH.text $ show session.messageCount ]
              ]
          , HH.div
              [ HP.class_ (H.ClassName "session-summary__row") ]
              [ HH.span
                  [ HP.class_ (H.ClassName "session-summary__label") ]
                  [ HH.text "Tokens:" ]
              , HH.span
                  [ HP.class_ (H.ClassName "session-summary__value") ]
                  [ HH.text $ show session.promptTokens <> " in / " <> show session.completionTokens <> " out" ]
              ]
          , HH.div
              [ HP.class_ (H.ClassName "session-summary__row") ]
              [ HH.span
                  [ HP.class_ (H.ClassName "session-summary__label") ]
                  [ HH.text "Cost:" ]
              , HH.span
                  [ HP.class_ (H.ClassName "session-summary__value") ]
                  [ HH.text $ formatUSD session.cost ]
              ]
          , HH.div
              [ HP.class_ (H.ClassName "session-summary__row") ]
              [ HH.span
                  [ HP.class_ (H.ClassName "session-summary__label") ]
                  [ HH.text "Duration:" ]
              , HH.span
                  [ HP.class_ (H.ClassName "session-summary__value") ]
                  [ HH.text state.duration ]
              ]
          ]
      ]
