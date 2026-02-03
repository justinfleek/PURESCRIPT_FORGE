-- | Icon Component
-- |
-- | Icon definitions as pure data.
-- | Represents SVG icon structure without rendering.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/component/icon.tsx
module Forge.Console.App.Component.Icon
  ( IconType(..)
  , IconSize(..)
  , IconProps
  , getIconViewBox
  , getIconPath
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- | Available icon types
data IconType
  = IconLogo
  | IconCopy
  | IconCheck
  | IconCreditCard
  | IconStripe
  | IconChevron
  | IconChevronLeft
  | IconChevronRight
  | IconWorkspaceLogo
  | IconOpenAI
  | IconAnthropic
  | IconXai
  | IconAlibaba
  | IconMoonshotAI
  | IconZai
  | IconMiniMax
  | IconGemini
  | IconStealth
  | IconBreakdown

derive instance eqIconType :: Eq IconType

instance showIconType :: Show IconType where
  show IconLogo = "logo"
  show IconCopy = "copy"
  show IconCheck = "check"
  show IconCreditCard = "credit-card"
  show IconStripe = "stripe"
  show IconChevron = "chevron"
  show IconChevronLeft = "chevron-left"
  show IconChevronRight = "chevron-right"
  show IconWorkspaceLogo = "workspace-logo"
  show IconOpenAI = "openai"
  show IconAnthropic = "anthropic"
  show IconXai = "xai"
  show IconAlibaba = "alibaba"
  show IconMoonshotAI = "moonshot-ai"
  show IconZai = "zai"
  show IconMiniMax = "minimax"
  show IconGemini = "gemini"
  show IconStealth = "stealth"
  show IconBreakdown = "breakdown"

-- | Icon sizes
data IconSize
  = Small   -- 16x16
  | Medium  -- 24x24
  | Large   -- 32x32

derive instance eqIconSize :: Eq IconSize

-- | Icon props
type IconProps =
  { iconType :: IconType
  , size :: IconSize
  , className :: Maybe String
  }

-- | Get SVG viewBox for icon
getIconViewBox :: IconType -> String
getIconViewBox icon = case icon of
  IconLogo -> "0 0 64 32"
  IconCopy -> "0 0 24 24"
  IconCheck -> "0 0 24 24"
  IconCreditCard -> "0 0 24 24"
  IconStripe -> "0 0 24 24"
  IconChevron -> "0 0 8 6"
  IconChevronLeft -> "0 0 20 20"
  IconChevronRight -> "0 0 20 20"
  IconWorkspaceLogo -> "0 0 24 30"
  IconOpenAI -> "0 0 22 22"
  IconAnthropic -> "0 0 24 24"
  IconXai -> "0 0 24 24"
  IconAlibaba -> "0 0 22 22"
  IconMoonshotAI -> "0 0 24 24"
  IconZai -> "0 0 24 24"
  IconMiniMax -> "0 0 24 24"
  IconGemini -> "0 0 50 50"
  IconStealth -> "0 0 24 18"
  IconBreakdown -> "0 0 16 16"

-- | Get SVG path data for icon (simplified - full paths are in rendering layer)
getIconPath :: IconType -> String
getIconPath icon = case icon of
  IconChevron -> "M4 5.04L7.374 1.667L6.667 0.96L4 3.626L1.334 0.96L0.626 1.667L4 5.04Z"
  IconChevronLeft -> "M12 15L7 10L12 5"
  IconChevronRight -> "M8 5L13 10L8 15"
  _ -> ""  -- Complex paths handled in rendering layer
