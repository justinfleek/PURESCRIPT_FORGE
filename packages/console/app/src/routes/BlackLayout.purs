-- | Black Layout Route
-- |
-- | Layout wrapper for OpenCode Black subscription pages.
-- | Provides dark theme header, spotlight animation, and footer.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/black.tsx
-- | Migrated: 2026-02-03
module Console.App.Routes.BlackLayout
  ( -- Types
    BlackLayoutProps
  , BlackLayoutState
  , BlackLayoutAction(..)
  , SpotlightAnimationState
  , SvgLightingValues
  , BlackPageMetadata
    -- State management
  , initialState
  , reduce
    -- Animation
  , defaultSpotlightConfig
  , calculateSvgLighting
    -- Metadata
  , pageMetadata
    -- Footer
  , footerLinks
  , FooterLink
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Console.App.Config as Config
import Data.Number (sin)

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Black layout props
type BlackLayoutProps =
  { starCount :: Maybe String
  }

-- | Spotlight animation state
type SpotlightAnimationState =
  { time :: Number
  , intensity :: Number
  , pulseValue :: Number
  }

-- | SVG lighting computed values
type SvgLightingValues =
  { glowIntensity :: Number
  , fillOpacity :: Number
  , strokeBrightness :: Number
  , shimmerPos :: Number
  , shimmerIntensity :: Number
  }

-- | Black layout state
type BlackLayoutState =
  { starCount :: String
  , spotlightState :: SpotlightAnimationState
  , svgLighting :: SvgLightingValues
  }

-- | Black layout actions
data BlackLayoutAction
  = Initialize
  | UpdateSpotlight SpotlightAnimationState
  | SetStarCount String

derive instance eqBlackLayoutAction :: Eq BlackLayoutAction

instance showBlackLayoutAction :: Show BlackLayoutAction where
  show Initialize = "Initialize"
  show (UpdateSpotlight s) = "(UpdateSpotlight " <> show s.time <> ")"
  show (SetStarCount c) = "(SetStarCount " <> c <> ")"

-- | Page metadata for Black pages
type BlackPageMetadata =
  { title :: String
  , description :: String
  , canonicalUrl :: String
  , ogType :: String
  , ogImage :: String
  , twitterCard :: String
  }

-- | Footer link
type FooterLink =
  { label :: String
  , url :: String
  , isExternal :: Boolean
  , starCount :: Maybe String
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- STATE MANAGEMENT
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Default spotlight animation state
defaultSpotlightState :: SpotlightAnimationState
defaultSpotlightState =
  { time: 0.0
  , intensity: 0.5
  , pulseValue: 1.0
  }

-- | Default SVG lighting values
defaultSvgLighting :: SvgLightingValues
defaultSvgLighting =
  { glowIntensity: 0.175
  , fillOpacity: 0.14
  , strokeBrightness: 67.5
  , shimmerPos: 0.5
  , shimmerIntensity: 0.075
  }

-- | Initial state
initialState :: BlackLayoutProps -> BlackLayoutState
initialState props =
  { starCount: case props.starCount of
      Just s -> s
      Nothing -> Config.github.starsFormatted.compact
  , spotlightState: defaultSpotlightState
  , svgLighting: defaultSvgLighting
  }

-- | Pure reducer
reduce :: BlackLayoutAction -> BlackLayoutState -> BlackLayoutState
reduce action state = case action of
  Initialize -> state
  
  UpdateSpotlight spotlightState ->
    state 
      { spotlightState = spotlightState
      , svgLighting = calculateSvgLighting spotlightState
      }
  
  SetStarCount count ->
    state { starCount = count }

-- ═══════════════════════════════════════════════════════════════════════════════
-- ANIMATION
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Default spotlight configuration
defaultSpotlightConfig :: { enabled :: Boolean }
defaultSpotlightConfig = { enabled: true }

-- | Calculate SVG lighting values from spotlight state
-- | Port of the createMemo from black.tsx
calculateSvgLighting :: SpotlightAnimationState -> SvgLightingValues
calculateSvgLighting state =
  let
    t = state.time
    
    -- Wave functions for animation
    wave1 = sin (t * 1.5) * 0.5 + 0.5
    wave2 = sin (t * 2.3 + 1.2) * 0.5 + 0.5
    wave3 = sin (t * 0.8 + 2.5) * 0.5 + 0.5
    
    shimmerPos = sin (t * 0.7) * 0.5 + 0.5
    glowIntensity = max (state.intensity * state.pulseValue * 0.35) 0.15
    fillOpacity = max (0.1 + wave1 * 0.08 * state.pulseValue) 0.12
    strokeBrightness = max (55.0 + wave2 * 25.0 * state.pulseValue) 60.0
    shimmerIntensity = max (wave3 * 0.15 * state.pulseValue) 0.08
  in
    { glowIntensity
    , fillOpacity
    , strokeBrightness
    , shimmerPos
    , shimmerIntensity
    }

-- ═══════════════════════════════════════════════════════════════════════════════
-- METADATA
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Page metadata for Black section
pageMetadata :: BlackPageMetadata
pageMetadata =
  { title: "OpenCode Black | Access all the world's best coding models"
  , description: "Get access to Claude, GPT, Gemini and more with OpenCode Black subscription plans."
  , canonicalUrl: Config.baseUrl <> "/black"
  , ogType: "website"
  , ogImage: "/social-share-black.png"
  , twitterCard: "summary_large_image"
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- FOOTER
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Build footer links
footerLinks :: String -> Array FooterLink
footerLinks starCount =
  [ { label: "GitHub"
    , url: Config.github.repoUrl
    , isExternal: true
    , starCount: Just starCount
    }
  , { label: "Docs"
    , url: "/docs"
    , isExternal: false
    , starCount: Nothing
    }
  , { label: "Privacy"
    , url: "/legal/privacy-policy"
    , isExternal: false
    , starCount: Nothing
    }
  , { label: "Terms"
    , url: "/legal/terms-of-service"
    , isExternal: false
    , starCount: Nothing
    }
  ]

-- | Hero content
type HeroContent =
  { headline :: String
  , subheadline :: String
  }

heroContent :: HeroContent
heroContent =
  { headline: "Access all the world's best coding models"
  , subheadline: "Including Claude, GPT, Gemini and more"
  }

-- | Copyright text
copyrightText :: Int -> String
copyrightText year = "©" <> show year <> " Anomaly"

anomalyUrl :: String
anomalyUrl = "https://anoma.ly"
