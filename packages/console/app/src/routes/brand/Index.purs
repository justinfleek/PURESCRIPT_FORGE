-- | Brand Index Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/brand/index.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Brand.Index
  ( BrandAsset(..)
  , AssetFormat(..)
  , AssetVariant(..)
  , allBrandAssets
  , getAssetFilename
  , getAssetDownloadUrl
  , brandAssetsZipUrl
  ) where

import Prelude

import Data.Array (filter)
import Data.Maybe (Maybe(..))

-- | Asset format type
data AssetFormat = PNG | SVG

derive instance eqAssetFormat :: Eq AssetFormat

instance showAssetFormat :: Show AssetFormat where
  show PNG = "png"
  show SVG = "svg"

-- | Asset variant (light/dark)
data AssetVariant = Light | Dark

derive instance eqAssetVariant :: Eq AssetVariant

instance showAssetVariant :: Show AssetVariant where
  show Light = "light"
  show Dark = "dark"

-- | Asset type
data AssetType
  = Logo
  | Wordmark
  | WordmarkSimple

derive instance eqAssetType :: Eq AssetType

instance showAssetType :: Show AssetType where
  show Logo = "logo"
  show Wordmark = "wordmark"
  show WordmarkSimple = "wordmark-simple"

-- | Brand asset definition
type BrandAsset =
  { assetType :: AssetType
  , variant :: AssetVariant
  , format :: AssetFormat
  , previewUrl :: String
  , downloadUrl :: String
  }

-- | Build asset filename
getAssetFilename :: AssetType -> AssetVariant -> AssetFormat -> String
getAssetFilename assetType variant format =
  "opencode-" <> show assetType <> "-" <> show variant <> "." <> show format

-- | Build asset download URL
getAssetDownloadUrl :: AssetType -> AssetVariant -> AssetFormat -> String
getAssetDownloadUrl assetType variant format =
  "/asset/brand/" <> getAssetFilename assetType variant format

-- | Build preview URL
getPreviewUrl :: AssetType -> AssetVariant -> String
getPreviewUrl assetType variant =
  "/asset/brand/preview-opencode-" <> show assetType <> "-" <> show variant <> ".png"

-- | All brand assets
allBrandAssets :: Array BrandAsset
allBrandAssets =
  [ mkAsset Logo Light
  , mkAsset Logo Dark
  , mkAsset Wordmark Light
  , mkAsset Wordmark Dark
  , mkAsset WordmarkSimple Light
  , mkAsset WordmarkSimple Dark
  ]
  where
    mkAsset :: AssetType -> AssetVariant -> BrandAsset
    mkAsset assetType variant =
      { assetType
      , variant
      , format: PNG  -- Default format for display
      , previewUrl: getPreviewUrl assetType variant
      , downloadUrl: getAssetDownloadUrl assetType variant PNG
      }

-- | Brand assets ZIP URL
brandAssetsZipUrl :: String
brandAssetsZipUrl = "/opencode-brand-assets.zip"

-- | Page metadata
type PageMeta =
  { title :: String
  , description :: String
  , canonicalPath :: String
  }

brandPageMeta :: PageMeta
brandPageMeta =
  { title: "OpenCode | Brand"
  , description: "OpenCode brand guidelines"
  , canonicalPath: "/brand"
  }

-- | Filter assets by variant
getAssetsByVariant :: AssetVariant -> Array BrandAsset
getAssetsByVariant variant = filter (\a -> a.variant == variant) allBrandAssets

-- | Filter assets by type
getAssetsByType :: AssetType -> Array BrandAsset
getAssetsByType assetType = filter (\a -> a.assetType == assetType) allBrandAssets
