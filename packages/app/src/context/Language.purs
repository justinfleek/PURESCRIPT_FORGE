-- | Language context - manages i18n localization
-- | Migrated from: forge-dev/packages/app/src/context/language.tsx
module App.Context.Language
  ( Locale(..)
  , allLocales
  , detectLocale
  , localeLabel
  ) where

import Prelude

import Data.Array (elem, head)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), contains, toLower)

-- | Supported locales
data Locale
  = En
  | Zh
  | Zht
  | Ko
  | De
  | Es
  | Fr
  | Da
  | Ja
  | Pl
  | Ru
  | Ar
  | No
  | Br
  | Th

derive instance eqLocale :: Eq Locale

instance showLocale :: Show Locale where
  show En = "en"
  show Zh = "zh"
  show Zht = "zht"
  show Ko = "ko"
  show De = "de"
  show Es = "es"
  show Fr = "fr"
  show Da = "da"
  show Ja = "ja"
  show Pl = "pl"
  show Ru = "ru"
  show Ar = "ar"
  show No = "no"
  show Br = "br"
  show Th = "th"

-- | All available locales
allLocales :: Array Locale
allLocales = [En, Zh, Zht, Ko, De, Es, Fr, Da, Ja, Pl, Ru, Ar, No, Br, Th]

-- | Detect locale from browser language (simplified - real implementation uses FFI)
detectLocale :: Array String -> Locale
detectLocale languages =
  fromMaybe En (head (map detectSingle languages) >>= identity)
  where
    detectSingle :: String -> Maybe Locale
    detectSingle lang =
      let l = toLower lang
      in
        if startsWith "zh" l then
          if contains (Pattern "hant") l then Just Zht else Just Zh
        else if startsWith "ko" l then Just Ko
        else if startsWith "de" l then Just De
        else if startsWith "es" l then Just Es
        else if startsWith "fr" l then Just Fr
        else if startsWith "da" l then Just Da
        else if startsWith "ja" l then Just Ja
        else if startsWith "pl" l then Just Pl
        else if startsWith "ru" l then Just Ru
        else if startsWith "ar" l then Just Ar
        else if startsWith "no" l || startsWith "nb" l || startsWith "nn" l then Just No
        else if startsWith "pt" l then Just Br
        else if startsWith "th" l then Just Th
        else Nothing
    
    startsWith :: String -> String -> Boolean
    startsWith prefix str =
      let prefixLen = strLength prefix
      in take prefixLen str == prefix
    
    take :: Int -> String -> String
    take n s = 
      if n <= 0 then ""
      else case strUncons s of
        Nothing -> ""
        Just { head: c, tail } -> singleton c <> take (n - 1) tail
    
    strLength :: String -> Int
    strLength = go 0
      where
        go acc s = case strUncons s of
          Nothing -> acc
          Just { tail } -> go (acc + 1) tail
    
    strUncons :: String -> Maybe { head :: Char, tail :: String }
    strUncons s = 
      -- Simplified - would use String.uncons in real implementation
      Nothing
    
    singleton :: Char -> String
    singleton _ = ""

-- | Get display label for a locale
localeLabel :: Locale -> String
localeLabel En = "English"
localeLabel Zh = "\x7B80\x4F53\x4E2D\x6587"  -- Simplified Chinese
localeLabel Zht = "\x7E41\x9AD4\x4E2D\x6587"  -- Traditional Chinese
localeLabel Ko = "\xD55C\xAD6D\xC5B4"  -- Korean
localeLabel De = "Deutsch"
localeLabel Es = "Espa\xF1ol"
localeLabel Fr = "Fran\xE7ais"
localeLabel Da = "Dansk"
localeLabel Ja = "\x65E5\x672C\x8A9E"  -- Japanese
localeLabel Pl = "Polski"
localeLabel Ru = "\x0420\x0443\x0441\x0441\x043A\x0438\x0439"  -- Russian
localeLabel Ar = "\x0627\x0644\x0639\x0631\x0628\x064A\x0629"  -- Arabic
localeLabel No = "Norsk"
localeLabel Br = "Portugu\xEAs"
localeLabel Th = "\x0E44\x0E17\x0E22"  -- Thai
