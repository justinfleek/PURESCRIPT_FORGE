-- | Locale utilities (formatting and localization)
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/locale.ts
module Forge.Util.Locale
  ( titlecase
  , time
  , datetime
  , todayTimeOrDateTime
  , number
  , duration
  , truncate
  , truncateMiddle
  , pluralize
  ) where

import Prelude

-- | Convert string to title case
foreign import titlecase :: String -> String

-- | Format timestamp as time (short)
foreign import time :: Number -> String

-- | Format timestamp as datetime
foreign import datetime :: Number -> String

-- | Format as time if today, otherwise datetime
foreign import todayTimeOrDateTime :: Number -> String

-- | Format number with K/M suffixes
foreign import number :: Number -> String

-- | Format duration in human readable form
foreign import duration :: Number -> String

-- | Truncate string at end with ellipsis
foreign import truncate :: String -> Int -> String

-- | Truncate string in middle with ellipsis
foreign import truncateMiddle :: String -> Int -> String

-- | Pluralize based on count
foreign import pluralize :: Int -> String -> String -> String
