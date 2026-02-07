-- | Model Types and Data - Venice Model Information
-- |
-- | **What:** Defines types and data for Venice models, including capabilities, pricing,
-- |         and metadata for model selection and comparison.
-- | **Why:** Provides structured data about available models to enable informed model
-- |         selection based on use case, cost, and performance characteristics.
-- | **How:** Defines Model type with all relevant metadata, provides model catalog,
-- |         and utility functions for filtering and comparing models.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.Projection`: ModelPricing type (reused)
-- |
-- | **Mathematical Foundation:**
-- | - **Model Comparison:** Models are compared by parameters, speed, quality, and cost
-- | - **Filtering:** Models can be filtered by size, type, speed tier, and search query
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Model as Model
-- |
-- | -- Get all models
-- | allModels = Model.allModels
-- |
-- | -- Filter by size
-- | largeModels = Model.filterBySize Model.Large allModels
-- |
-- | -- Find model by ID
-- | model = Model.findById "llama-3.3-70b" allModels
-- | ```
-- |
-- | Based on spec 16-MODEL-SELECTION.md
module Sidepanel.Model where

import Prelude
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Sidepanel.Projection (ModelPricing)

-- | Model size category
data ModelSize = Small | Medium | Large | XLarge

derive instance eqModelSize :: Eq ModelSize

-- | Model type/category
data ModelType = General | Code | Reasoning | Math

derive instance eqModelType :: Eq ModelType

-- | Speed tier (relative speed rating)
data SpeedTier = Slow | Medium | Fast | VeryFast

derive instance eqSpeedTier :: Eq SpeedTier

-- | Quality tier (relative quality rating)
data QualityTier = Basic | Good | Excellent | Outstanding

derive instance eqQualityTier :: Eq QualityTier

-- | Model information - Complete model metadata
-- |
-- | **Purpose:** Represents a Venice model with all relevant information for selection.
-- | **Fields:**
-- | - `id`: Model identifier (e.g., "llama-3.3-70b")
-- | - `name`: Display name
-- | - `displayName`: Full display name
-- | - `provider`: Always "venice"
-- | - `size`: Model size category
-- | - `parameters`: Parameter count in billions
-- | - `contextWindow`: Context window size in tokens
-- | - `speed`: Speed tier (relative)
-- | - `quality`: Quality tier (relative)
-- | - `pricing`: Pricing per 1K tokens
-- | - `bestFor`: Array of use case descriptions
-- | - `weaknesses`: Array of weakness descriptions
-- | - `isRecommended`: Whether this is a recommended model
type Model =
  { id :: String
  , name :: String
  , displayName :: String
  , provider :: String  -- Always "venice"
  , size :: ModelSize
  , parameters :: Int  -- Billions
  , contextWindow :: Int  -- Tokens
  , speed :: SpeedTier
  , quality :: QualityTier
  , pricing :: ModelPricing
  , bestFor :: Array String
  , weaknesses :: Array String
  , isRecommended :: Boolean
  }

-- | All available Venice models
allModels :: Array Model
allModels =
  [ { id: "llama-3.3-70b"
    , name: "llama-3.3-70b"
    , displayName: "Llama 3.3 70B"
    , provider: "venice"
    , size: Large
    , parameters: 70
    , contextWindow: 128000
    , speed: Fast
    , quality: Excellent
    , pricing: { inputPer1K: 0.0007, outputPer1K: 0.0007 }
    , bestFor: [ "General coding", "Debugging", "Explanations" ]
    , weaknesses: [ "Slightly slower on generation" ]
    , isRecommended: true
    }
  , { id: "qwen-2.5-72b"
    , name: "qwen-2.5-72b"
    , displayName: "Qwen 2.5 72B"
    , provider: "venice"
    , size: Large
    , parameters: 72
    , contextWindow: 128000
    , speed: Fast
    , quality: Excellent
    , pricing: { inputPer1K: 0.0008, outputPer1K: 0.0008 }
    , bestFor: [ "Strong reasoning", "Math proofs", "Algorithms" ]
    , weaknesses: []
    , isRecommended: false
    }
  , { id: "deepseek-r1-70b"
    , name: "deepseek-r1-70b"
    , displayName: "DeepSeek R1 70B"
    , provider: "venice"
    , size: Large
    , parameters: 70
    , contextWindow: 64000
    , speed: Fast
    , quality: Excellent
    , pricing: { inputPer1K: 0.0006, outputPer1K: 0.0006 }
    , bestFor: [ "Code generation", "Refactoring" ]
    , weaknesses: [ "Smaller context", "Less versatile" ]
    , isRecommended: false
    }
  , { id: "llama-3.1-405b"
    , name: "llama-3.1-405b"
    , displayName: "Llama 3.1 405B"
    , provider: "venice"
    , size: XLarge
    , parameters: 405
    , contextWindow: 128000
    , speed: Slow
    , quality: Outstanding
    , pricing: { inputPer1K: 0.002, outputPer1K: 0.002 }
    , bestFor: [ "Complex architecture", "Deep analysis" ]
    , weaknesses: [ "Slower", "More expensive" ]
    , isRecommended: false
    }
  , { id: "qwen-2.5-32b"
    , name: "qwen-2.5-32b"
    , displayName: "Qwen 2.5 32B"
    , provider: "venice"
    , size: Medium
    , parameters: 32
    , contextWindow: 128000
    , speed: Fast
    , quality: Good
    , pricing: { inputPer1K: 0.0004, outputPer1K: 0.0004 }
    , bestFor: [ "Quick questions", "Simple code" ]
    , weaknesses: [ "Lower quality than larger models" ]
    , isRecommended: false
    }
  , { id: "qwen-2.5-7b"
    , name: "qwen-2.5-7b"
    , displayName: "Qwen 2.5 7B"
    , provider: "venice"
    , size: Small
    , parameters: 7
    , contextWindow: 128000
    , speed: VeryFast
    , quality: Basic
    , pricing: { inputPer1K: 0.0001, outputPer1K: 0.0001 }
    , bestFor: [ "Simple tasks", "High volume" ]
    , weaknesses: [ "Lower quality", "Limited capability" ]
    , isRecommended: false
    }
  ]

-- | Find model by ID - Lookup model by identifier
-- |
-- | **Purpose:** Finds a model in the catalog by its ID.
-- | **Parameters:**
-- | - `id`: Model identifier
-- | **Returns:** Maybe Model (Nothing if not found)
findById :: String -> Maybe Model
findById id = Array.find (\m -> m.id == id) allModels

-- | Filter models by size - Filter models by size category
-- |
-- | **Purpose:** Filters models by size category (Small, Medium, Large, XLarge).
filterBySize :: ModelSize -> Array Model -> Array Model
filterBySize size = Array.filter (\m -> m.size == size)

-- | Filter models by type - Filter models by type/category
-- |
-- | **Purpose:** Filters models by type (General, Code, Reasoning, Math).
-- | **Note:** Currently all models are General type. Type filtering would require
-- |          additional metadata on models.
filterByType :: ModelType -> Array Model -> Array Model
filterByType _ = identity  -- Would filter by type if models had type metadata

-- | Filter models by speed - Filter models by speed tier
-- |
-- | **Purpose:** Filters models by speed tier (Slow, Medium, Fast, VeryFast).
filterBySpeed :: SpeedTier -> Array Model -> Array Model
filterBySpeed speed = Array.filter (\m -> m.speed == speed)

-- | Search models - Search models by name or description
-- |
-- | **Purpose:** Searches models by name, display name, or bestFor descriptions.
-- | **Parameters:**
-- | - `query`: Search query string
-- | - `models`: Models to search
-- | **Returns:** Filtered array of models matching query
searchModels :: String -> Array Model -> Array Model
searchModels query models =
  let
    lowerQuery = String.toLower query
    matches :: Model -> Boolean
    matches model =
      String.contains (String.Pattern lowerQuery) (String.toLower model.name) ||
      String.contains (String.Pattern lowerQuery) (String.toLower model.displayName) ||
      Array.any (\desc -> String.contains (String.Pattern lowerQuery) (String.toLower desc)) model.bestFor
  in
    Array.filter matches models

-- | Get recommended models - Get models marked as recommended
-- |
-- | **Purpose:** Returns all recommended models (typically the best default choices).
getRecommended :: Array Model -> Array Model
getRecommended = Array.filter _.isRecommended

-- | Compare models - Compare two models side-by-side
-- |
-- | **Purpose:** Creates a comparison structure for two models.
-- | **Returns:** Comparison data with differences highlighted
type ModelComparison =
  { model1 :: Model
  , model2 :: Model
  , differences :: Array String
  }

compareModels :: Model -> Model -> ModelComparison
compareModels m1 m2 =
  let
    differences = Array.catMaybes
      [ if m1.parameters /= m2.parameters then
          Just $ "Parameters: " <> show m1.parameters <> "B vs " <> show m2.parameters <> "B"
        else Nothing
      , if m1.contextWindow /= m2.contextWindow then
          Just $ "Context: " <> show m1.contextWindow <> " vs " <> show m2.contextWindow <> " tokens"
        else Nothing
      , if m1.speed /= m2.speed then
          Just $ "Speed: " <> showSpeedTier m1.speed <> " vs " <> showSpeedTier m2.speed
        else Nothing
      , if m1.quality /= m2.quality then
          Just $ "Quality: " <> showQualityTier m1.quality <> " vs " <> showQualityTier m2.quality
        else Nothing
      ]
  in
    { model1: m1, model2: m2, differences }

showSpeedTier :: SpeedTier -> String
showSpeedTier = case _ of
  Slow -> "Slow"
  Medium -> "Medium"
  Fast -> "Fast"
  VeryFast -> "Very Fast"

showQualityTier :: QualityTier -> String
showQualityTier = case _ of
  Basic -> "Basic"
  Good -> "Good"
  Excellent -> "Excellent"
  Outstanding -> "Outstanding"

showModelSize :: ModelSize -> String
showModelSize = case _ of
  Small -> "Small"
  Medium -> "Medium"
  Large -> "Large"
  XLarge -> "XLarge"
