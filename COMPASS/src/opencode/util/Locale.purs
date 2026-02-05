-- | Locale utilities
module Opencode.Util.Locale where

import Prelude
import Effect (Effect)
import Data.String as String

-- | Get current locale
getLocale :: Effect String
getLocale = getSystemLocale
  where
    foreign import getSystemLocale :: Effect String

-- | Format number for locale
formatNumber :: Number -> String -> String
formatNumber n locale = formatNumberForLocale n locale
  where
    foreign import formatNumberForLocale :: Number -> String -> String

-- | Format date for locale
formatDate :: Number -> String -> String
formatDate timestamp locale = formatDateForLocale timestamp locale
  where
    foreign import formatDateForLocale :: Number -> String -> String
