-- | Privacy Policy Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/legal/privacy-policy/index.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Legal.PrivacyPolicy
  ( PrivacyPolicyMeta(..)
  , TableOfContentsItem(..)
  , privacyPolicyMeta
  , tableOfContents
  , effectiveDate
  ) where

import Prelude

-- | Page metadata
type PrivacyPolicyMeta =
  { title :: String
  , description :: String
  , canonicalPath :: String
  }

-- | Privacy policy page metadata
privacyPolicyMeta :: PrivacyPolicyMeta
privacyPolicyMeta =
  { title: "OpenCode | Privacy Policy"
  , description: "OpenCode privacy policy"
  , canonicalPath: "/legal/privacy-policy"
  }

-- | Effective date
effectiveDate :: String
effectiveDate = "Dec 16, 2025"

-- | Table of contents item
type TableOfContentsItem =
  { id :: String
  , title :: String
  , children :: Array TableOfContentsItem
  }

-- | Table of contents
tableOfContents :: Array TableOfContentsItem
tableOfContents =
  [ { id: "what-this-privacy-policy-covers"
    , title: "What this Privacy Policy Covers"
    , children: []
    }
  , { id: "personal-data"
    , title: "Personal Data"
    , children:
        [ { id: "categories-of-personal-data", title: "Categories of Personal Data We Collect", children: [] }
        , { id: "commercial-purposes", title: "Our Commercial or Business Purposes for Collecting Personal Data", children: [] }
        , { id: "other-permitted-purposes", title: "Other Permitted Purposes for Processing Personal Data", children: [] }
        , { id: "categories-of-sources", title: "Categories of Sources of Personal Data", children: [] }
        ]
    }
  , { id: "how-we-disclose"
    , title: "How We Disclose Your Personal Data"
    , children: []
    }
  , { id: "tracking-tools"
    , title: "Tracking Tools and Opt-Out"
    , children: []
    }
  , { id: "data-security"
    , title: "Data Security"
    , children: []
    }
  , { id: "personal-data-of-children"
    , title: "Personal Data of Children"
    , children: []
    }
  , { id: "california-resident-rights"
    , title: "California Resident Rights (\"CCPA\")"
    , children: []
    }
  , { id: "contact-information"
    , title: "Contact Information"
    , children: []
    }
  ]

-- | Contact email
contactEmail :: String
contactEmail = "contact@anoma.ly"
