-- | Desktop Feedback Redirect Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/desktop-feedback.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.DesktopFeedback
  ( feedbackDiscordUrl
  , handleGet
  ) where

import Prelude

-- | Discord feedback channel URL
feedbackDiscordUrl :: String
feedbackDiscordUrl = "https://discord.gg/h5TNnkFVNy"

-- | Handle GET request (pure)
-- | Returns redirect configuration
handleGet :: { redirectUrl :: String, status :: Int }
handleGet = { redirectUrl: feedbackDiscordUrl, status: 302 }
