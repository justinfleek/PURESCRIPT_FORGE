-- | Locale utilities
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/util/locale.ts
module Forge.Util.Locale where

import Prelude
import Effect (Effect)
import Forge.Util.NotImplemented (notImplemented)

-- | Get current locale
getLocale :: Effect String
getLocale = notImplemented "Util.Locale.getLocale"

-- | Format number for locale
formatNumber :: Number -> String -> String
formatNumber n locale = show n -- TODO: Implement proper formatting

-- | Format date for locale
formatDate :: Number -> String -> String
formatDate timestamp locale = "" -- TODO: Implement
