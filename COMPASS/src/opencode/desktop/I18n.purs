-- | Desktop I18n - Internationalization
-- | Phase 5: Desktop/Web Migration
module Opencode.Desktop.I18n where

import Prelude

import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String as String

-- | Translation key type
type TranslationKey = String

-- | Translation parameters
type TranslationParams = Map.Map String String

-- | Initialize i18n system
initI18n :: Aff Unit
initI18n = do
  -- Detect locale from navigator
  detectedLocale <- detectLocale # liftEffect
  -- Try to load saved locale from store
  savedLocale <- loadSavedLocale
  -- Use saved locale if available, otherwise use detected
  let locale = fromMaybe detectedLocale savedLocale
  -- Set the locale
  setLocale locale # liftEffect

-- | Detect locale from navigator
foreign import detectLocale :: Effect String

-- | Load saved locale from Tauri store
foreign import loadSavedLocale :: Aff (Maybe String)

-- | Translate a key with parameters
t :: TranslationKey -> TranslationParams -> Aff String
t key params = do
  locale <- getLocale # liftEffect
  translations <- getTranslations locale # liftEffect
  case Map.lookup key translations of
    Just template -> pure $ interpolate template params
    Nothing -> pure key

-- | Get current locale
foreign import getLocale :: Effect String

-- | Set locale
foreign import setLocale :: String -> Effect Unit

-- | Get translations for locale
foreign import getTranslations :: String -> Effect (Map.Map String String)

-- | Interpolate template with parameters
-- | Supports both {{key}} and {key} patterns for compatibility
interpolate :: String -> TranslationParams -> String
interpolate template params =
  Map.foldlWithKey (\acc key value -> 
    let pattern1 = String.Pattern ("{{" <> key <> "}}")
        pattern2 = String.Pattern ("{" <> key <> "}")
        replacement = String.Replacement value
    in String.replaceAll pattern1 replacement (String.replaceAll pattern2 replacement acc)
  ) template params
