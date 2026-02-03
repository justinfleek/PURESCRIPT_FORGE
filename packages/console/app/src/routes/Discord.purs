-- | Discord Redirect Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/discord.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Discord
  ( discordInviteUrl
  , handleGet
  ) where

import Prelude

-- | Discord invite URL
discordInviteUrl :: String
discordInviteUrl = "https://discord.gg/opencode"

-- | Handle GET request (pure)
-- | Returns redirect configuration
handleGet :: { redirectUrl :: String, status :: Int }
handleGet = { redirectUrl: discordInviteUrl, status: 302 }
