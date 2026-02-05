-- | Home Page Landing
-- |
-- | Pure data representation for the OpenCode landing page.
-- | Separates content data from rendering logic following functional patterns.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/index.tsx
-- | Migrated: 2026-02-03
module Console.App.Routes.Index
  ( -- Types
    HomePageMetadata
  , HeroContent
  , InstallMethod(..)
  , InstallCommand
  , Feature
  , GrowthStat
  , FaqItem
  , DesktopBanner
    -- Data
  , pageMetadata
  , heroContent
  , installMethods
  , features
  , growthStats
  , faqItems
  , privacyContent
  , zenCtaContent
  , desktopBanner
    -- Utilities
  , installCommandText
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Console.App.Config as Config

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Page metadata for SEO
type HomePageMetadata =
  { title :: String
  , description :: String
  , canonicalUrl :: String
  , ogImage :: String
  , twitterImage :: String
  }

-- | Desktop app banner content
type DesktopBanner =
  { badge :: String
  , text :: String
  , platforms :: String
  , linkText :: String
  , linkTextMobile :: String
  , linkUrl :: String
  }

-- | Hero section content
type HeroContent =
  { headline :: String
  , description :: String
  }

-- | Install method identifiers
data InstallMethod
  = Curl
  | Npm
  | Bun
  | Brew
  | Paru

derive instance eqInstallMethod :: Eq InstallMethod
derive instance ordInstallMethod :: Ord InstallMethod

instance showInstallMethod :: Show InstallMethod where
  show = case _ of
    Curl -> "curl"
    Npm -> "npm"
    Bun -> "bun"
    Brew -> "brew"
    Paru -> "paru"

-- | Install command data
type InstallCommand =
  { method :: InstallMethod
  , prefix :: String
  , highlight :: String
  , suffix :: String
  }

-- | Feature item
type Feature =
  { marker :: String
  , title :: String
  , description :: String
  }

-- | Growth statistics
type GrowthStat =
  { figure :: String
  , label :: String
  , value :: String
  }

-- | FAQ item
type FaqItem =
  { question :: String
  , answer :: String
  , links :: Array { text :: String, url :: String }
  }

-- | Privacy section content
type PrivacyContent =
  { title :: String
  , description :: String
  , learnMoreUrl :: String
  }

-- | Zen CTA section content
type ZenCtaContent =
  { headline :: String
  , description :: String
  , linkText :: String
  , linkUrl :: String
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- DATA
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Page metadata
pageMetadata :: HomePageMetadata
pageMetadata =
  { title: "OpenCode | The open source AI coding agent"
  , description: "OpenCode is an open source agent that helps you write code. Free models included or connect any model from any provider."
  , canonicalUrl: Config.baseUrl
  , ogImage: "/social-share.png"
  , twitterImage: "/social-share.png"
  }

-- | Desktop app banner
desktopBanner :: DesktopBanner
desktopBanner =
  { badge: "New"
  , text: "Desktop app available in beta"
  , platforms: " on macOS, Windows, and Linux"
  , linkText: "Download now"
  , linkTextMobile: "Download the desktop beta now"
  , linkUrl: "/download"
  }

-- | Hero section content
heroContent :: HeroContent
heroContent =
  { headline: "The open source AI coding agent"
  , description: "Free models included or connect any model from any provider, including Claude, GPT, Gemini and more."
  }

-- | Install methods with commands
installMethods :: Array InstallCommand
installMethods =
  [ { method: Curl
    , prefix: "curl -fsSL "
    , highlight: "https://opencode.ai/install"
    , suffix: " | bash"
    }
  , { method: Npm
    , prefix: "npm i -g "
    , highlight: "opencode-ai"
    , suffix: ""
    }
  , { method: Bun
    , prefix: "bun add -g "
    , highlight: "opencode-ai"
    , suffix: ""
    }
  , { method: Brew
    , prefix: "brew install "
    , highlight: "anomalyco/tap/opencode"
    , suffix: ""
    }
  , { method: Paru
    , prefix: "paru -S "
    , highlight: "opencode"
    , suffix: ""
    }
  ]

-- | "What is OpenCode" features
features :: Array Feature
features =
  [ { marker: "[*]"
    , title: "LSP enabled"
    , description: "Automatically loads the right LSPs for the LLM"
    }
  , { marker: "[*]"
    , title: "Multi-session"
    , description: "Start multiple agents in parallel on the same project"
    }
  , { marker: "[*]"
    , title: "Share links"
    , description: "Share a link to any session for reference or to debug"
    }
  , { marker: "[*]"
    , title: "GitHub Copilot"
    , description: "Log in with GitHub to use your Copilot account"
    }
  , { marker: "[*]"
    , title: "ChatGPT Plus/Pro"
    , description: "Log in with OpenAI to use your ChatGPT Plus or Pro account"
    }
  , { marker: "[*]"
    , title: "Any model"
    , description: "75+ LLM providers through Models.dev, including local models"
    }
  , { marker: "[*]"
    , title: "Any editor"
    , description: "Available as a terminal interface, desktop app, and IDE extension"
    }
  ]

-- | Growth statistics
growthStats :: Array GrowthStat
growthStats =
  [ { figure: "Fig 1."
    , label: "GitHub Stars"
    , value: Config.github.starsFormatted.compact
    }
  , { figure: "Fig 2."
    , label: "Contributors"
    , value: Config.stats.contributors
    }
  , { figure: "Fig 3."
    , label: "Monthly Devs"
    , value: Config.stats.monthlyUsers
    }
  ]

-- | Privacy section content
privacyContent :: PrivacyContent
privacyContent =
  { title: "Built for privacy first"
  , description: "OpenCode does not store any of your code or context data, so that it can operate in privacy sensitive environments."
  , learnMoreUrl: "/docs/enterprise/"
  }

-- | FAQ items
faqItems :: Array FaqItem
faqItems =
  [ { question: "What is OpenCode?"
    , answer: "OpenCode is an open source agent that helps you write and run code with any AI model. It's available as a terminal-based interface, desktop app, or IDE extension."
    , links: []
    }
  , { question: "How do I use OpenCode?"
    , answer: "The easiest way to get started is to read the"
    , links: [{ text: "intro", url: "/docs" }]
    }
  , { question: "Do I need extra AI subscriptions to use OpenCode?"
    , answer: "Not necessarily, OpenCode comes with a set of free models that you can use without creating an account. Aside from these, you can use any of the popular coding models by creating a Zen account. While we encourage users to use Zen, OpenCode also works with all popular providers such as OpenAI, Anthropic, xAI etc. You can even connect your local models."
    , links: 
        [ { text: "Zen", url: "/zen" }
        , { text: "local models", url: "/docs/providers/#lm-studio" }
        ]
    }
  , { question: "Can I use my existing AI subscriptions with OpenCode?"
    , answer: "Yes, OpenCode supports subscription plans from all major providers. You can use your Claude Pro/Max, ChatGPT Plus/Pro, or GitHub Copilot subscriptions."
    , links: [{ text: "Learn more", url: "/docs/providers/#directory" }]
    }
  , { question: "Can I only use OpenCode in the terminal?"
    , answer: "Not anymore! OpenCode is now available as an app for your desktop and web!"
    , links: 
        [ { text: "desktop", url: "/download" }
        , { text: "web", url: "/docs/web" }
        ]
    }
  , { question: "How much does OpenCode cost?"
    , answer: "OpenCode is 100% free to use. It also comes with a set of free models. There might be additional costs if you connect any other provider."
    , links: []
    }
  , { question: "What about data and privacy?"
    , answer: "Your data and information is only stored when you use our free models or create sharable links."
    , links: 
        [ { text: "our models", url: "/docs/zen/#privacy" }
        , { text: "share pages", url: "/docs/share/#privacy" }
        ]
    }
  , { question: "Is OpenCode open source?"
    , answer: "Yes, OpenCode is fully open source. The source code is public on GitHub under the MIT License, meaning anyone can use, modify, or contribute to its development. Anyone from the community can file issues, submit pull requests, and extend functionality."
    , links: 
        [ { text: "GitHub", url: Config.github.repoUrl }
        , { text: "MIT License", url: Config.github.repoUrl <> "?tab=MIT-1-ov-file#readme" }
        ]
    }
  ]

-- | Zen CTA section content
zenCtaContent :: ZenCtaContent
zenCtaContent =
  { headline: "Access reliable optimized models for coding agents"
  , description: "Zen gives you access to a handpicked set of AI models that OpenCode has tested and benchmarked specifically for coding agents. No need to worry about inconsistent performance and quality across providers, use validated models that work."
  , linkText: "Learn about Zen"
  , linkUrl: "/zen"
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- UTILITIES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get the full command text for an install method
installCommandText :: InstallCommand -> String
installCommandText cmd = cmd.prefix <> cmd.highlight <> cmd.suffix

-- | Get install command by method
findInstallMethod :: InstallMethod -> Maybe InstallCommand
findInstallMethod method = Array.find (\cmd -> cmd.method == method) installMethods
