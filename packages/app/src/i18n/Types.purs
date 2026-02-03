-- | I18n type definitions
-- | Migrated from forge-dev/packages/app/src/i18n/*.ts
module Forge.App.I18n.Types
  ( Language(..)
  , Dict
  , allLanguages
  , languageCode
  , languageName
  ) where

import Prelude
import Foreign.Object (Object)

-- | Supported languages
data Language
  = English
  | ChineseSimplified
  | ChineseTraditional
  | Korean
  | German
  | Spanish
  | French
  | Danish
  | Japanese
  | Polish
  | Russian
  | Arabic
  | Norwegian
  | Portuguese
  | Thai

derive instance eqLanguage :: Eq Language
derive instance ordLanguage :: Ord Language

-- | Dictionary type
type Dict = Object String

-- | All supported languages
allLanguages :: Array Language
allLanguages =
  [ English
  , ChineseSimplified
  , ChineseTraditional
  , Korean
  , German
  , Spanish
  , French
  , Danish
  , Japanese
  , Polish
  , Russian
  , Arabic
  , Norwegian
  , Portuguese
  , Thai
  ]

-- | Get language code
languageCode :: Language -> String
languageCode English = "en"
languageCode ChineseSimplified = "zh"
languageCode ChineseTraditional = "zht"
languageCode Korean = "ko"
languageCode German = "de"
languageCode Spanish = "es"
languageCode French = "fr"
languageCode Danish = "da"
languageCode Japanese = "ja"
languageCode Polish = "pl"
languageCode Russian = "ru"
languageCode Arabic = "ar"
languageCode Norwegian = "no"
languageCode Portuguese = "br"
languageCode Thai = "th"

-- | Get native language name
languageName :: Language -> String
languageName English = "English"
languageName ChineseSimplified = "简体中文"
languageName ChineseTraditional = "繁體中文"
languageName Korean = "한국어"
languageName German = "Deutsch"
languageName Spanish = "Español"
languageName French = "Français"
languageName Danish = "Dansk"
languageName Japanese = "日本語"
languageName Polish = "Polski"
languageName Russian = "Русский"
languageName Arabic = "العربية"
languageName Norwegian = "Norsk"
languageName Portuguese = "Português (Brasil)"
languageName Thai = "ไทย"
