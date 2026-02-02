-- | App Helper Functions
-- |
-- | Utility functions for the root application component.
-- |
-- | Coeffect Equation:
-- |   Helpers : Domain -> Codomain
-- |   where each helper performs a pure transformation
-- |
-- | Module Coverage: Route conversion, settings conversion, session extraction
module Sidepanel.App.Helpers
  ( routeNameToRoute
  , convertSettingsToAppState
  , convertBalanceUpdatePayload
  , getSessionForRoute
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Sidepanel.Router (Route(..))
import Sidepanel.State.AppState (AppState, AppSettings)
import Sidepanel.State.Settings (Settings as FullSettings, Theme(..))
import Sidepanel.State.Actions (BalanceUpdate)
import Sidepanel.Api.Types (BalanceUpdatePayload)
import Sidepanel.Components.Session.SessionPanel as SessionPanel
import Sidepanel.Theme.Prism (MonitorType(..))

--------------------------------------------------------------------------------
-- | Route Conversion
--------------------------------------------------------------------------------

-- | Convert route name string to Route
routeNameToRoute :: String -> Route
routeNameToRoute name = case name of
  "dashboard" -> Dashboard
  "timeline" -> Timeline
  "file-context" -> FileContext
  "terminal" -> Terminal
  "settings" -> Settings
  "proof" -> Proof
  "diff" -> DiffViewer
  _ -> Dashboard

--------------------------------------------------------------------------------
-- | Settings Conversion
--------------------------------------------------------------------------------

-- | Convert FullSettings to AppSettings
convertSettingsToAppState :: FullSettings -> AppSettings
convertSettingsToAppState fullSettings =
  { veniceApiKey: Nothing
  , opencodeApiUrl: "http://localhost:4096"
  , leanLspUrl: Nothing
  , monitorType: case fullSettings.appearance.theme of
      Dark -> OLED
      Light -> LCD
      System -> OLED
  , blackBalance: 0.11
  }

--------------------------------------------------------------------------------
-- | Balance Conversion
--------------------------------------------------------------------------------

-- | Convert BalanceUpdatePayload to BalanceUpdate
convertBalanceUpdatePayload :: BalanceUpdatePayload -> BalanceUpdate
convertBalanceUpdatePayload payload =
  { diem: payload.diem
  , flk: payload.flk
  , usd: payload.usd
  , effective: payload.effective
  , consumptionRate: payload.consumptionRate
  , timeToDepletion: payload.timeToDepletion
  , todayUsed: payload.todayUsed
  }

--------------------------------------------------------------------------------
-- | Session Extraction
--------------------------------------------------------------------------------

-- | Get session for route
getSessionForRoute :: AppState -> Maybe String -> Maybe SessionPanel.Session
getSessionForRoute appState sessionId = case appState.session of
  Just session ->
    Just
      { id: session.id
      , model: session.model
      , provider: "venice"
      , startedAt: session.startedAt
      , promptTokens: session.promptTokens
      , completionTokens: session.completionTokens
      , cost: session.cost
      , messages: []
      }
  Nothing -> Nothing
