-- | I18n Context - Internationalization Provider
-- |
-- | Provides localization context with template parameter support.
-- | Uses English as fallback when translations are missing.
-- |
-- | Source: _OTHER/opencode-original/packages/ui/src/context/i18n.tsx
module Forge.UI.Context.I18n
  ( I18nContext
  , I18nProvider
  , useI18n
  , UiI18nKey
  , UiI18nParams
  , resolveTemplate
  ) where

import Prelude

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), Replacement(..))
import Data.String as String
import Data.String.Regex (Regex, replace)
import Data.String.Regex.Flags (global)
import Data.String.Regex.Unsafe (unsafeRegex)
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Foreign.Object (Object)
import Foreign.Object as Object
import Halogen.HTML as HH

-- | I18n key type (string key into translation dictionary)
type UiI18nKey = String

-- | Parameters for template interpolation
type UiI18nParams = Object String

-- | I18n context interface
type I18nContext =
  { locale :: Effect String
  , t :: UiI18nKey -> Maybe UiI18nParams -> String
  }

-- | Regex for template placeholders: {{ key }}
templateRegex :: Regex
templateRegex = unsafeRegex "\\{\\{\\s*([^}]+?)\\s*\\}\\}" global

-- | Resolve template placeholders in text
resolveTemplate :: String -> Maybe UiI18nParams -> String
resolveTemplate text Nothing = text
resolveTemplate text (Just params) =
  -- Simple replacement for each param
  Object.foldl replaceParam text params
  where
    replaceParam :: String -> String -> String -> String
    replaceParam acc key value = 
      String.replaceAll 
        (Pattern ("{{" <> key <> "}}")) 
        (Replacement value) 
        acc

-- | Default English translations (subset for fallback)
defaultDict :: Object String
defaultDict = Object.fromFoldable
  [ "ui.common.cancel" /\ "Cancel"
  , "ui.common.confirm" /\ "Confirm"
  , "ui.common.close" /\ "Close"
  , "ui.common.submit" /\ "Submit"
  , "ui.common.add" /\ "Add"
  , "ui.common.dismiss" /\ "Dismiss"
  , "ui.common.next" /\ "Next"
  , "ui.list.loading" /\ "Loading"
  , "ui.list.empty" /\ "No results"
  ]

-- | Fallback I18n context using English
fallbackI18n :: I18nContext
fallbackI18n =
  { locale: pure "en"
  , t: \key mParams ->
      let text = fromMaybe key (Object.lookup key defaultDict)
      in resolveTemplate text mParams
  }

-- | Internal context reference  
foreign import i18nContextRef :: Ref (Maybe I18nContext)

-- | I18n provider props
type I18nProviderProps =
  { value :: I18nContext
  , children :: Array (HH.HTML Unit Unit)
  }

-- | I18n provider component
type I18nProvider = I18nProviderProps -> HH.HTML Unit Unit

-- | Use the I18n context (returns fallback if not in provider)
useI18n :: Effect I18nContext
useI18n = do
  mCtx <- Ref.read i18nContextRef
  pure $ fromMaybe fallbackI18n mCtx
