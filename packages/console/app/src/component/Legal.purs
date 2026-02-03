-- | Legal Component
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/component/legal.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Component.Legal
  ( LegalLink(..)
  , LegalLinks
  , Year
  , mkYear
  , currentYearPlaceholder
  , defaultLinks
  , brandLink
  , privacyLink
  , termsLink
  , externalLink
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- | Year type with validation
newtype Year = Year Int

derive instance eqYear :: Eq Year
derive instance ordYear :: Ord Year

instance showYear :: Show Year where
  show (Year y) = show y

-- | Smart constructor for year
mkYear :: Int -> Maybe Year
mkYear y
  | y >= 1970 && y <= 2100 = Just (Year y)
  | otherwise = Nothing

-- | Placeholder for current year (to be replaced at render time)
currentYearPlaceholder :: String
currentYearPlaceholder = "{{YEAR}}"

-- | Legal link type
data LegalLink
  = InternalLink { href :: String, label :: String }
  | ExternalLink { href :: String, label :: String }

derive instance eqLegalLink :: Eq LegalLink

instance showLegalLink :: Show LegalLink where
  show (InternalLink r) = "(InternalLink " <> show r.href <> " " <> show r.label <> ")"
  show (ExternalLink r) = "(ExternalLink " <> show r.href <> " " <> show r.label <> ")"

-- | Get href from any link type
linkHref :: LegalLink -> String
linkHref (InternalLink r) = r.href
linkHref (ExternalLink r) = r.href

-- | Get label from any link type
linkLabel :: LegalLink -> String
linkLabel (InternalLink r) = r.label
linkLabel (ExternalLink r) = r.label

-- | Check if link is external
isExternal :: LegalLink -> Boolean
isExternal (ExternalLink _) = true
isExternal (InternalLink _) = false

-- | Collection of legal links
type LegalLinks =
  { copyright :: { year :: String, company :: String, companyUrl :: String }
  , links :: Array LegalLink
  }

-- | External link helper
externalLink :: String -> String -> LegalLink
externalLink href label = ExternalLink { href, label }

-- | Internal link helper  
internalLink :: String -> String -> LegalLink
internalLink href label = InternalLink { href, label }

-- | Brand link
brandLink :: LegalLink
brandLink = internalLink "/brand" "Brand"

-- | Privacy policy link
privacyLink :: LegalLink
privacyLink = internalLink "/legal/privacy-policy" "Privacy"

-- | Terms of service link
termsLink :: LegalLink
termsLink = internalLink "/legal/terms-of-service" "Terms"

-- | Default links configuration matching source
defaultLinks :: LegalLinks
defaultLinks =
  { copyright:
      { year: currentYearPlaceholder
      , company: "Anomaly"
      , companyUrl: "https://anoma.ly"
      }
  , links:
      [ brandLink
      , privacyLink
      , termsLink
      ]
  }

-- | Copyright text builder (pure)
buildCopyrightText :: Year -> String -> String
buildCopyrightText (Year year) company =
  "\u00A9" <> show year <> " " <> company
