-- | Bridge API - Settings Operations
-- |
-- | User settings persistence through the bridge server.
-- |
-- | Coeffect Equation:
-- |   SettingsOps : WSClient -> SettingsRequest -> Aff (Either Error Response)
-- |   with persistence: Settings^1 -o Stored^1
-- |   where settings are durably persisted to storage
-- |
-- | Module Coverage: settings.save
module Sidepanel.Api.Bridge.Settings
  ( -- * Settings Operations
    saveSettings
  ) where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Argonaut.Core (Json)
import Argonaut.Decode (class DecodeJson, decodeJson, (.:))
import Argonaut.Encode (class EncodeJson, encodeJson)
import Sidepanel.WebSocket.Client (WSClient, request)
import Sidepanel.Api.Types (JsonRpcError)
import Sidepanel.Api.Bridge.Types
  ( SettingsSaveRequest
  , SettingsSaveResponse
  , printJsonDecodeError
  )

--------------------------------------------------------------------------------
-- | JSON Instances
--------------------------------------------------------------------------------

instance encodeSettingsSaveRequest :: EncodeJson SettingsSaveRequest where
  encodeJson req = encodeJson
    { alerts: req.alerts
    , appearance: req.appearance
    , keyboard: req.keyboard
    , features: req.features
    , storage: req.storage
    }

instance decodeSettingsSaveResponse :: DecodeJson SettingsSaveResponse where
  decodeJson json = do
    obj <- decodeJson json
    success <- obj .: "success"
    pure { success }

--------------------------------------------------------------------------------
-- | Settings Operations
--------------------------------------------------------------------------------

-- | Save settings to bridge server
-- |
-- | Persists user settings including:
-- | - Alert thresholds (warning/critical percentages, hours, sound)
-- | - Appearance preferences (theme)
-- | - Keyboard settings (enabled, vim mode)
-- | - Feature toggles (countdown, charts, proof panel, timeline)
-- | - Storage configuration (retention days)
saveSettings :: WSClient -> SettingsSaveRequest -> Aff (Either JsonRpcError SettingsSaveResponse)
saveSettings client req = do
  result <- request client "settings.save" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError SettingsSaveResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right r -> pure $ Right r
