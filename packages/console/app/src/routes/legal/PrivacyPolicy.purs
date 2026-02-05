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

-- | Table of contents item (newtype to avoid cycle in type synonym)
newtype TableOfContentsItem = TableOfContentsItem
  { id :: String
  , title :: String
  , children :: Array TableOfContentsItem
  }

derive instance eqTableOfContentsItem :: Eq TableOfContentsItem

-- | Table of contents
tableOfContents :: Array TableOfContentsItem
tableOfContents =
  [ TableOfContentsItem { id: "what-this-privacy-policy-covers"
    , title: "What this Privacy Policy Covers"
    , children: []
    }
  , TableOfContentsItem { id: "personal-data"
    , title: "Personal Data"
    , children:
        [ TableOfContentsItem { id: "categories-of-personal-data", title: "Categories of Personal Data We Collect", children: [] }
        , TableOfContentsItem { id: "commercial-purposes", title: "Our Commercial or Business Purposes for Collecting Personal Data", children: [] }
        , TableOfContentsItem { id: "other-permitted-purposes", title: "Other Permitted Purposes for Processing Personal Data", children: [] }
        , TableOfContentsItem { id: "categories-of-sources", title: "Categories of Sources of Personal Data", children: [] }
        ]
    }
  , TableOfContentsItem { id: "how-we-disclose"
    , title: "How We Disclose Your Personal Data"
    , children: []
    }
  , TableOfContentsItem { id: "tracking-tools"
    , title: "Tracking Tools and Opt-Out"
    , children: []
    }
  , TableOfContentsItem { id: "data-security"
    , title: "Data Security"
    , children: []
    }
  , TableOfContentsItem { id: "personal-data-of-children"
    , title: "Personal Data of Children"
    , children: []
    }
  , TableOfContentsItem { id: "california-resident-rights"
    , title: "California Resident Rights (\"CCPA\")"
    , children: []
    }
  , TableOfContentsItem { id: "contact-information"
    , title: "Contact Information"
    , children: []
    }
  ]

-- | Contact email
contactEmail :: String
contactEmail = "contact@anoma.ly"
