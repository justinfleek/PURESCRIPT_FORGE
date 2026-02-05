-- | Omega Landing Page
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/omega/index.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Omega.Index
  ( OmegaPageContent(..)
  , Feature(..)
  , HowStep(..)
  , Testimonial(..)
  , FaqItem(..)
  , features
  , howSteps
  , testimonials
  , faqItems
  , pageMetadata
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- | Page metadata
type OmegaPageMetadata =
  { title :: String
  , canonicalPath :: String
  , ogImage :: String
  }

-- | Default page metadata
pageMetadata :: OmegaPageMetadata
pageMetadata =
  { title: "OpenCode Omega | A curated set of reliable optimized models for coding agents"
  , canonicalPath: "/omega"
  , ogImage: "/social-share-omega.png"
  }

-- | Page content
type OmegaPageContent =
  { heroTitle :: String
  , heroDescription :: String
  , pricingCopy :: String
  , pricingSubtext :: String
  , getStartedUrl :: String
  }

-- | Default page content
omegaPageContent :: OmegaPageContent
omegaPageContent =
  { heroTitle: "Reliable optimized models for coding agents"
  , heroDescription: "Omega gives you access to a curated set of AI models that OpenCode has tested and benchmarked specifically for coding agents. No need to worry about inconsistent performance and quality, use validated models that work."
  , pricingCopy: "Add $20 Pay as you go balance"
  , pricingSubtext: "(+$1.23 card processing fee)"
  , getStartedUrl: "/auth"
  }

-- | Problem section feature
type Feature =
  { marker :: String
  , description :: String
  }

-- | Features list
features :: Array Feature
features =
  [ { marker: "[*]", description: "Testing select models and consulting their teams" }
  , { marker: "[*]", description: "Working with providers to ensure they're delivered properly" }
  , { marker: "[*]", description: "Benchmarking all model-provider combinations we recommend" }
  ]

-- | How it works step
type HowStep =
  { step :: Int
  , title :: String
  , description :: String
  , linkUrl :: Maybe String
  , linkText :: Maybe String
  }

-- | How steps
howSteps :: Array HowStep
howSteps =
  [ { step: 1
    , title: "Sign up and add $20 balance"
    , description: "follow the"
    , linkUrl: Just "/docs/omega/#how-it-works"
    , linkText: Just "setup instructions"
    }
  , { step: 2
    , title: "Use Omega with transparent pricing"
    , description: "with zero markups"
    , linkUrl: Just "/docs/omega/#pricing"
    , linkText: Just "pay per request"
    }
  , { step: 3
    , title: "Auto-top up"
    , description: "when your balance reaches $5 we'll automatically add $20"
    , linkUrl: Nothing
    , linkText: Nothing
    }
  ]

-- | Testimonial
type Testimonial =
  { url :: String
  , name :: String
  , title :: String
  , quote :: String
  , avatarPath :: String
  }

-- | Testimonials
testimonials :: Array Testimonial
testimonials =
  [ { url: "https://x.com/thdxr/status/1973531687629017227"
    , name: "Dax Raad"
    , title: "ex-CEO, Terminal Products"
    , quote: "@OpenCode Omega has been life changing, it's truly a no-brainer."
    , avatarPath: "avatar-dax.png"
    }
  , { url: "https://x.com/jayair/status/1973530190870618456"
    , name: "Jay V"
    , title: "ex-Founder, SEED, PM, Melt, Pop, Dapt, Cadmus, and ViewPoint"
    , quote: "4 out of 5 people on our team love using @OpenCode Omega."
    , avatarPath: "avatar-jay.png"
    }
  , { url: "https://x.com/adamdotdev/status/1973732040718860563"
    , name: "Adam Elmore"
    , title: "ex-Hero, AWS"
    , quote: "I can't recommend @OpenCode Omega enough. Seriously, it's really good."
    , avatarPath: "avatar-adam.png"
    }
  , { url: "https://x.com/iamdavidhill/status/1973530568773214622"
    , name: "David Hill"
    , title: "ex-Head of Design, Laravel"
    , quote: "With @OpenCode Omega I know all the models are tested and perfect for coding agents."
    , avatarPath: "avatar-david.png"
    }
  , { url: "https://x.com/fanjiewang/status/1973530092736487756"
    , name: "Frank Wang"
    , title: "ex-Intern, Nvidia (4 times)"
    , quote: "I wish I was still at Nvidia."
    , avatarPath: "avatar-frank.png"
    }
  ]

-- | FAQ item
type FaqItem =
  { question :: String
  , answer :: String
  }

-- | FAQ items
faqItems :: Array FaqItem
faqItems =
  [ { question: "What is OpenCode Omega?"
    , answer: "Omega is a curated set of AI models tested and benchmarked for coding agents created by the team behind OpenCode."
    }
  , { question: "What makes Omega more accurate?"
    , answer: "Omega only provides models that have been specifically tested and benchmarked for coding agents. You wouldn't use a butter knife to cut steak, don't use poor models for coding."
    }
  , { question: "Is Omega cheaper?"
    , answer: "Omega is not for profit. Omega passes through the costs from the model providers to you. The higher Omega's usage the more OpenCode can negotiate better rates and pass those to you."
    }
  , { question: "How much does Omega cost?"
    , answer: "Omega charges per request with zero markups, so you pay exactly what the model provider charges. Your total cost depends on usage, and you can set monthly spend limits in your account. To cover costs, OpenCode adds only a small payment processing fee of $1.23 per $20 balance top-up."
    }
  , { question: "What about data and privacy?"
    , answer: "All Omega models are hosted in the US. Providers follow a zero-retention policy and do not use your data for model training, with the following exceptions."
    }
  , { question: "Can I set spend limits?"
    , answer: "Yes, you can set monthly spending limits in your account."
    }
  , { question: "Can I cancel?"
    , answer: "Yes, you can disable billing at any time and use your remaining balance."
    }
  , { question: "Can I use Omega with other coding agents?"
    , answer: "While Omega works great with OpenCode, you can use Omega with any agent. Follow the setup instructions in your preferred coding agent."
    }
  ]

-- | Privacy notice
type PrivacyNotice =
  { title :: String
  , description :: String
  , linkUrl :: String
  }

-- | Default privacy notice
privacyNotice :: PrivacyNotice
privacyNotice =
  { title: "Your privacy is important to us"
  , description: "All Omega models are hosted in the US. Providers follow a zero-retention policy and do not use your data for model training."
  , linkUrl: "/docs/omega/#privacy"
  }

-- | Model logos (provider icons shown in hero)
type ModelLogo =
  { name :: String
  }

-- | Model logos to display
modelLogos :: Array ModelLogo
modelLogos =
  [ { name: "anthropic" }
  , { name: "openai" }
  , { name: "gemini" }
  , { name: "xai" }
  , { name: "minimax" }
  , { name: "kimi" }
  , { name: "zai" }
  ]
