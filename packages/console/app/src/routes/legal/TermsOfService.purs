-- | Terms of Service Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/legal/terms-of-service/index.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Legal.TermsOfService
  ( TermsOfServiceMeta(..)
  , termsOfServiceMeta
  , effectiveDate
  , contactEmail
  ) where

import Prelude

-- | Page metadata
type TermsOfServiceMeta =
  { title :: String
  , description :: String
  , canonicalPath :: String
  }

-- | Terms of service page metadata
termsOfServiceMeta :: TermsOfServiceMeta
termsOfServiceMeta =
  { title: "OpenCode | Terms of Service"
  , description: "OpenCode terms of service"
  , canonicalPath: "/legal/terms-of-service"
  }

-- | Effective date
effectiveDate :: String
effectiveDate = "Dec 16, 2025"

-- | Contact email
contactEmail :: String
contactEmail = "contact@anoma.ly"

-- | Company name
companyName :: String
companyName = "ANOMALY INNOVATIONS, INC."
