-- | I18n module - translation lookup
-- | Migrated from opencode-dev/packages/app/src/i18n/*.ts
module Opencode.App.I18n
  ( module Opencode.App.I18n.Types
  , translate
  , t
  , getDictionary
  ) where

import Prelude
import Data.Maybe (fromMaybe)
import Foreign.Object (Object, lookup)
import Opencode.App.I18n.Types (Language(..), Dict, allLanguages, languageCode, languageName)
import Opencode.App.I18n.En as En

-- | Get translation for a key
translate :: Language -> String -> String
translate lang key = fromMaybe key (lookup key (getDictionary lang))

-- | Alias for translate
t :: Language -> String -> String
t = translate

-- | Get dictionary for language
-- | Falls back to English for missing translations
getDictionary :: Language -> Dict
getDictionary English = En.dict
getDictionary _ = En.dict  -- TODO: Add other languages
