{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : PrismColor.FFI
-- Description : JSON interface for external tools
-- 
-- Provides JSON encoding/decoding for communication with:
-- - VSCode extension (TypeScript)
-- - Neovim plugin (Lua)
-- - Emacs package (Elisp)
-- 
-- The interface accepts a ThemeConfig and returns [ThemeVariant].

module PrismColor.FFI
  ( -- * JSON Interface
    generateThemesFromJSON
  , parseThemeConfig
  , encodeVariants
  
    -- * FFI Config (alternative format from TypeScript)
  , FFIThemeConfig(..)
  , ffiConfigToThemeConfig
  ) where

import Data.Aeson
import Data.Aeson.Types (parseMaybe)
import qualified Data.ByteString.Lazy as BL
import qualified Data.Text as T
import GHC.Generics (Generic)

import PrismColor.Types
import PrismColor.Palette

-- | Alternative config format matching TypeScript interface
data FFIThemeConfig = FFIThemeConfig
  { ffiBaseColor :: FFIColorConfig
  , ffiHeroColor :: FFIColorConfig
  , ffiMonitorType :: T.Text
  , ffiBlackBalance :: Double
  , ffiMode :: T.Text
  }
  deriving (Eq, Show, Generic)

data FFIColorConfig = FFIColorConfig
  { ffiHue :: Double
  , ffiSaturation :: Double
  , ffiLightness :: Double
  }
  deriving (Eq, Show, Generic)

instance FromJSON FFIThemeConfig where
  parseJSON = withObject "FFIThemeConfig" $ \v -> FFIThemeConfig
    <$> v .: "baseColor"
    <*> v .: "heroColor"
    <*> v .: "monitorType"
    <*> v .: "blackBalance"
    <*> v .: "mode"

instance FromJSON FFIColorConfig where
  parseJSON = withObject "FFIColorConfig" $ \v -> FFIColorConfig
    <$> v .: "hue"
    <*> v .: "saturation"
    <*> v .: "lightness"

-- | Convert FFI config format to internal ThemeConfig
ffiConfigToThemeConfig :: FFIThemeConfig -> Maybe ThemeConfig
ffiConfigToThemeConfig FFIThemeConfig{..} = do
  baseHue <- mkHue ffiHue <|> Just (normalizeHue ffiHue)
  baseSat <- mkUnitInterval ffiSaturation <|> Just (clampUnit ffiSaturation)
  heroHue <- mkHue (ffiHue ffiHeroColor) <|> Just (normalizeHue (ffiHue ffiHeroColor))
  heroSat <- mkUnitInterval (ffiSaturation ffiHeroColor) <|> Just (clampUnit (ffiSaturation ffiHeroColor))
  bb <- mkBlackBalance ffiBlackBalance <|> Just (BlackBalance (max 0 (min 0.2 ffiBlackBalance)))
  
  let monType = case ffiMonitorType of
        "LCD" -> LCD
        _     -> OLED
      
      mode = case ffiMode of
        "light" -> Light
        _       -> Dark
  
  pure ThemeConfig
    { configBaseHue = fromMaybe (normalizeHue (ffiHue ffiBaseColor)) baseHue
    , configBaseSaturation = fromMaybe (clampUnit (ffiSaturation ffiBaseColor)) baseSat
    , configHeroHue = fromMaybe (normalizeHue (ffiHue ffiHeroColor)) heroHue
    , configHeroSaturation = fromMaybe (clampUnit (ffiSaturation ffiHeroColor)) heroSat
    , configMonitorType = monType
    , configBlackBalance = bb
    , configMode = mode
    }
  where
    (<|>) :: Maybe a -> Maybe a -> Maybe a
    Nothing <|> y = y
    x       <|> _ = x
    
    fromMaybe :: a -> Maybe a -> a
    fromMaybe def Nothing = def
    fromMaybe _ (Just x)  = x

-- | Parse ThemeConfig from JSON bytes
parseThemeConfig :: BL.ByteString -> Maybe ThemeConfig
parseThemeConfig bs = do
  ffiConfig <- decode bs
  ffiConfigToThemeConfig ffiConfig

-- | Encode variants to JSON bytes
encodeVariants :: [ThemeVariant] -> BL.ByteString
encodeVariants = encode . object . (:[]) . ("variants" .=)

-- | Main FFI entry point: JSON in → JSON out
-- 
-- Input:  {"baseColor": {...}, "heroColor": {...}, ...}
-- Output: {"variants": [...]}
generateThemesFromJSON :: BL.ByteString -> BL.ByteString
generateThemesFromJSON input =
  case parseThemeConfig input of
    Nothing -> encode $ object ["error" .= ("Invalid theme config" :: T.Text)]
    Just config -> 
      let variants = generateVariants config
      in encode $ object ["variants" .= variants]
