-- | Theme Types - Color and Theme Definitions
-- |
-- | Type definitions for the theming system including:
-- | - Color types (Hex, RGB, OKLCH) with bounded values
-- | - PRISM color spaces (sRGB, LinearRGB, XYZ, OKLAB, OKLCH)
-- | - Monitor calibration (OLED vs LCD black balance)
-- | - Base16 semantic color palette
-- | - Theme variants (light/dark)
-- |
-- | Based on PRISM color science with Lean4 proofs.
-- | Source: _OTHER/opencode-original/packages/ui/src/theme/types.ts
-- | Reference: src/prism-lean/PrismColor/Basic.lean
module Forge.UI.Theme.Types
  ( -- * Bounded Value Types
    UnitInterval
  , mkUnitInterval
  , clampUnit
  , unUnit
  , Hue
  , mkHue
  , normalizeHue
  , unHue
  
    -- * Color Spaces
  , HexColor
  , RGB
  , SRGB
  , LinearRGB
  , XYZ
  , OKLAB
  , OKLCH
  , mkOKLCH
  
    -- * Monitor Calibration
  , MonitorType(..)
  , BlackBalance
  , mkBlackBalance
  , defaultBlackBalance
  , unBlackBalance
  
    -- * Theme Mode
  , ThemeMode(..)
  
    -- * Base16 Palette (Semantic Colors)
  , Base16Palette
  , Base16Slot(..)
  
    -- * Theme Configuration
  , ThemeConfig
  , ThemeSeedColors
  , ThemeVariant
  , DesktopTheme
  
    -- * Token System
  , TokenCategory(..)
  , ThemeToken
  , CssVarRef
  , ColorValue
  , ResolvedTheme
  ) where

import Prelude

import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Math (floor, max, min)

-------------------------------------------------------------------------------
-- BOUNDED VALUE TYPES (mirroring Lean4 UnitInterval/Hue proofs)
-------------------------------------------------------------------------------

-- | Value bounded in [0, 1] - mirrors Lean4 UnitInterval structure
-- | Invariant: 0 <= val <= 1 (enforced by smart constructors)
newtype UnitInterval = UnitInterval Number

derive instance eqUnitInterval :: Eq UnitInterval
derive instance ordUnitInterval :: Ord UnitInterval

instance showUnitInterval :: Show UnitInterval where
  show (UnitInterval v) = "(UnitInterval " <> show v <> ")"

-- | Smart constructor that validates bounds, returns Nothing if invalid
mkUnitInterval :: Number -> Maybe UnitInterval
mkUnitInterval x
  | x >= 0.0 && x <= 1.0 = Just (UnitInterval x)
  | otherwise = Nothing

-- | Clamp any number to [0, 1] - always succeeds
clampUnit :: Number -> UnitInterval
clampUnit x = UnitInterval (max 0.0 (min 1.0 x))

-- | Extract raw value
unUnit :: UnitInterval -> Number
unUnit (UnitInterval v) = v

-- | Hue angle in degrees [0, 360) - mirrors Lean4 Hue structure
-- | Invariant: 0 <= degrees < 360 (enforced by smart constructors)
newtype Hue = Hue Number

derive instance eqHue :: Eq Hue

instance showHue :: Show Hue where
  show (Hue h) = "(Hue " <> show h <> ")"

-- | Smart constructor that validates bounds
mkHue :: Number -> Maybe Hue
mkHue x
  | x >= 0.0 && x < 360.0 = Just (Hue x)
  | otherwise = Nothing

-- | Normalize any angle to [0, 360) using modular arithmetic
-- | Mirrors Lean4 Hue.normalize with same mathematical properties
normalizeHue :: Number -> Hue
normalizeHue x = 
  let normalized = x - 360.0 * floor (x / 360.0)
  in Hue normalized

-- | Extract raw hue degrees
unHue :: Hue -> Number
unHue (Hue h) = h

-------------------------------------------------------------------------------
-- COLOR SPACE TYPES
-------------------------------------------------------------------------------

-- | Hex color in format #RRGGBB or #RGB
type HexColor = String

-- | RGB color with values 0-1 (unbounded for intermediate calculations)
type RGB = { r :: Number, g :: Number, b :: Number }

-- | sRGB color space - gamma-corrected device color
-- | This is the standard web color format
type SRGB = 
  { r :: UnitInterval
  , g :: UnitInterval
  , b :: UnitInterval
  }

-- | Linear RGB - physical light intensity, no gamma
-- | Used as intermediate in color space conversions
type LinearRGB = 
  { r :: UnitInterval
  , g :: UnitInterval
  , b :: UnitInterval
  }

-- | CIE XYZ color space with D65 white point
-- | Y component is luminance (used for WCAG contrast)
type XYZ = 
  { x :: Number  -- Non-negative
  , y :: Number  -- Luminance (non-negative)
  , z :: Number  -- Non-negative
  }

-- | OKLAB perceptually uniform color space
-- | - L: Lightness [0, 1]
-- | - a: Green-Red axis (typically [-0.4, 0.4])
-- | - b: Blue-Yellow axis (typically [-0.4, 0.4])
type OKLAB = 
  { l :: UnitInterval
  , a :: Number
  , b :: Number
  }

-- | OKLCH cylindrical form of OKLAB - THE core type for PRISM
-- | - L: Lightness [0, 1] - perceptually uniform brightness
-- | - C: Chroma >= 0 - saturation/colorfulness
-- | - H: Hue [0, 360) - the color angle
-- |
-- | Key insight: OKLCH separates brightness from color, enabling
-- | perceptually uniform palettes where equal L steps look equally different.
type OKLCH = 
  { l :: UnitInterval
  , c :: Number  -- Chroma >= 0, typically [0, 0.4]
  , h :: Hue
  }

-- | Smart constructor for OKLCH with validation
mkOKLCH :: Number -> Number -> Number -> OKLCH
mkOKLCH l c h = 
  { l: clampUnit l
  , c: max 0.0 c
  , h: normalizeHue h
  }

-------------------------------------------------------------------------------
-- MONITOR CALIBRATION
-------------------------------------------------------------------------------

-- | Monitor type affects optimal black balance for readability
-- | - OLED: Pure blacks possible, but "black smear" at very low values
-- | - LCD: Backlight bleed means true black is impossible
data MonitorType
  = OLED  -- Optimal black balance ~11%
  | LCD   -- Optimal black balance ~16%

derive instance eqMonitorType :: Eq MonitorType

instance showMonitorType :: Show MonitorType where
  show OLED = "OLED"
  show LCD = "LCD"

-- | Black balance as a bounded percentage [0, 0.20]
-- | This is the minimum lightness for backgrounds to ensure readability
newtype BlackBalance = BlackBalance Number

derive instance eqBlackBalance :: Eq BlackBalance
derive instance ordBlackBalance :: Ord BlackBalance

instance showBlackBalance :: Show BlackBalance where
  show (BlackBalance v) = "(BlackBalance " <> show v <> ")"

-- | Smart constructor for black balance
mkBlackBalance :: Number -> Maybe BlackBalance
mkBlackBalance x
  | x >= 0.0 && x <= 0.20 = Just (BlackBalance x)
  | otherwise = Nothing

-- | Default black balance for monitor type
-- | Based on perceptual research documented in PRISM
defaultBlackBalance :: MonitorType -> BlackBalance
defaultBlackBalance OLED = BlackBalance 0.11
defaultBlackBalance LCD = BlackBalance 0.16

-- | Extract raw black balance value
unBlackBalance :: BlackBalance -> Number
unBlackBalance (BlackBalance v) = v

-------------------------------------------------------------------------------
-- THEME MODE
-------------------------------------------------------------------------------

-- | Theme mode (light or dark)
data ThemeMode
  = Dark
  | Light

derive instance eqThemeMode :: Eq ThemeMode

instance showThemeMode :: Show ThemeMode where
  show Dark = "Dark"
  show Light = "Light"

-------------------------------------------------------------------------------
-- BASE16 SEMANTIC PALETTE
-------------------------------------------------------------------------------

-- | Base16 color slots with semantic meaning
-- | This is the foundation of the PRISM theming system
data Base16Slot
  = Base00  -- Background (darkest/lightest)
  | Base01  -- Lighter/darker background
  | Base02  -- Selection background
  | Base03  -- Comments, secondary text
  | Base04  -- Dark/light foreground
  | Base05  -- Default foreground
  | Base06  -- Light/dark foreground
  | Base07  -- Brightest (white/black)
  | Base08  -- Error, red semantic
  | Base09  -- Warning, orange semantic
  | Base0A  -- Hero accent (user's chosen color)
  | Base0B  -- Success, green semantic
  | Base0C  -- Info, cyan semantic
  | Base0D  -- Link, blue semantic
  | Base0E  -- Special, purple semantic
  | Base0F  -- Deprecated, muted

derive instance eqBase16Slot :: Eq Base16Slot
derive instance ordBase16Slot :: Ord Base16Slot

instance showBase16Slot :: Show Base16Slot where
  show Base00 = "base00"
  show Base01 = "base01"
  show Base02 = "base02"
  show Base03 = "base03"
  show Base04 = "base04"
  show Base05 = "base05"
  show Base06 = "base06"
  show Base07 = "base07"
  show Base08 = "base08"
  show Base09 = "base09"
  show Base0A = "base0A"
  show Base0B = "base0B"
  show Base0C = "base0C"
  show Base0D = "base0D"
  show Base0E = "base0E"
  show Base0F = "base0F"

-- | Base16 color palette - 16 semantic color slots
-- | All colors are hex strings for compatibility with CSS
type Base16Palette = 
  { base00 :: HexColor  -- Background
  , base01 :: HexColor  -- Lighter background
  , base02 :: HexColor  -- Selection
  , base03 :: HexColor  -- Comments
  , base04 :: HexColor  -- Dark foreground
  , base05 :: HexColor  -- Default foreground
  , base06 :: HexColor  -- Light foreground
  , base07 :: HexColor  -- Brightest
  , base08 :: HexColor  -- Error/Red
  , base09 :: HexColor  -- Warning/Orange
  , base0A :: HexColor  -- Hero accent
  , base0B :: HexColor  -- Success/Green
  , base0C :: HexColor  -- Info/Cyan
  , base0D :: HexColor  -- Link/Blue
  , base0E :: HexColor  -- Special/Purple
  , base0F :: HexColor  -- Deprecated
  }

-------------------------------------------------------------------------------
-- THEME CONFIGURATION
-------------------------------------------------------------------------------

-- | Theme configuration for palette generation
type ThemeConfig = 
  { baseHue :: Hue                -- Base hue for backgrounds/foregrounds
  , baseSaturation :: UnitInterval -- Saturation for base colors
  , heroHue :: Hue                -- Hero accent hue (user's color)
  , heroSaturation :: UnitInterval -- Hero accent saturation
  , monitorType :: MonitorType    -- OLED or LCD
  , blackBalance :: BlackBalance  -- Minimum background lightness
  , mode :: ThemeMode             -- Dark or Light
  }

-- | Seed colors for generating a theme palette (legacy compatibility)
type ThemeSeedColors =
  { neutral :: HexColor
  , primary :: HexColor
  , success :: HexColor
  , warning :: HexColor
  , error :: HexColor
  , info :: HexColor
  , interactive :: HexColor
  , diffAdd :: HexColor
  , diffDelete :: HexColor
  }

-- | A theme variant (light or dark) with seeds and optional overrides
type ThemeVariant =
  { seeds :: ThemeSeedColors
  , overrides :: Map String ColorValue
  }

-- | A complete desktop theme with light and dark variants
type DesktopTheme =
  { name :: String
  , id :: String
  , light :: ThemeVariant
  , dark :: ThemeVariant
  }

-------------------------------------------------------------------------------
-- TOKEN SYSTEM
-------------------------------------------------------------------------------

-- | Token categories for organizing theme tokens
data TokenCategory
  = Background
  | Surface
  | Text
  | Border
  | Icon
  | Input
  | Button
  | Syntax
  | Markdown
  | Diff
  | Avatar

derive instance eqTokenCategory :: Eq TokenCategory
derive instance ordTokenCategory :: Ord TokenCategory

instance showTokenCategory :: Show TokenCategory where
  show Background = "background"
  show Surface = "surface"
  show Text = "text"
  show Border = "border"
  show Icon = "icon"
  show Input = "input"
  show Button = "button"
  show Syntax = "syntax"
  show Markdown = "markdown"
  show Diff = "diff"
  show Avatar = "avatar"

-- | Theme token (CSS custom property name)
type ThemeToken = String

-- | CSS variable reference
type CssVarRef = String

-- | Color value - either a hex color or CSS variable reference
type ColorValue = String

-- | Resolved theme with all tokens mapped to color values
type ResolvedTheme = Map ThemeToken ColorValue
