-- | Model Section - Model Management
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/model-section.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.ModelSection
  ( ModelInfo(..)
  , ModelsInfo(..)
  , Lab(..)
  , ModelWithLab(..)
  , ModelToggleFormData(..)
  , getModelLab
  , sortModels
  , buildModelsWithLab
  , modelPriority
  ) where

import Prelude

import Data.Array (filter, sortBy)
import Data.Maybe (Maybe(..))
import Data.Ord (compare, comparing)
import Data.String (take, length)

-- | AI Lab/Provider
data Lab
  = Anthropic
  | OpenAI
  | Google
  | MoonshotAI
  | Zai
  | Alibaba
  | XAI
  | MiniMax
  | Stealth

derive instance eqLab :: Eq Lab
derive instance ordLab :: Ord Lab

instance showLab :: Show Lab where
  show Anthropic = "Anthropic"
  show OpenAI = "OpenAI"
  show Google = "Google"
  show MoonshotAI = "Moonshot AI"
  show Zai = "Z.ai"
  show Alibaba = "Alibaba"
  show XAI = "xAI"
  show MiniMax = "MiniMax"
  show Stealth = "Stealth"

-- | Model info from server
type ModelInfo =
  { id :: String
  , name :: String
  }

-- | Models info response
type ModelsInfo =
  { all :: Array ModelInfo
  , disabled :: Array String
  }

-- | Model with lab info
type ModelWithLab =
  { id :: String
  , name :: String
  , lab :: Lab
  }

-- | Check if string starts with prefix
startsWith :: String -> String -> Boolean
startsWith prefix str = take (length prefix) str == prefix

-- | Get lab for a model based on ID prefix
getModelLab :: String -> Lab
getModelLab modelId
  | startsWith "claude" modelId = Anthropic
  | startsWith "gpt" modelId = OpenAI
  | startsWith "gemini" modelId = Google
  | startsWith "kimi" modelId = MoonshotAI
  | startsWith "glm" modelId = Zai
  | startsWith "qwen" modelId = Alibaba
  | startsWith "minimax" modelId = MiniMax
  | startsWith "grok" modelId = XAI
  | otherwise = Stealth

-- | Model priority for sorting
-- | Lower number = higher priority
modelPriority :: String -> Int
modelPriority modelId
  | startsWith "big-pickle" modelId = 0
  | startsWith "minimax" modelId = 1
  | startsWith "grok" modelId = 2
  | startsWith "claude" modelId = 3
  | startsWith "gpt" modelId = 4
  | startsWith "gemini" modelId = 5
  | otherwise = 1000

-- | Sort models by priority and name
sortModels :: Array ModelInfo -> Array ModelInfo
sortModels models =
  sortBy compareModels models
  where
    compareModels :: ModelInfo -> ModelInfo -> Ordering
    compareModels a b =
      let
        priorityA = modelPriority a.id
        priorityB = modelPriority b.id
      in
        case compare priorityA priorityB of
          EQ -> compare a.name b.name
          other -> other

-- | Build models with lab info
buildModelsWithLab :: ModelsInfo -> Array ModelWithLab
buildModelsWithLab info =
  map addLab info.all
  where
    addLab :: ModelInfo -> ModelWithLab
    addLab model =
      { id: model.id
      , name: model.name
      , lab: getModelLab model.id
      }

-- | Check if model is enabled
isModelEnabled :: ModelsInfo -> String -> Boolean
isModelEnabled info modelId =
  not (elem modelId info.disabled)
  where
    elem :: String -> Array String -> Boolean
    elem x xs = case filter (\y -> y == x) xs of
      [] -> false
      _ -> true

-- | Form data for toggling model
type ModelToggleFormData =
  { model :: String
  , workspaceId :: String
  , enabled :: Boolean
  }

-- | Build form data for model toggle
buildToggleFormData :: String -> String -> Boolean -> ModelToggleFormData
buildToggleFormData model workspaceId enabled =
  { model
  , workspaceId
  , enabled
  }

-- | Validate model toggle form
validateToggleForm :: ModelToggleFormData -> Maybe String
validateToggleForm formData
  | formData.model == "" = Just "Model is required"
  | formData.workspaceId == "" = Just "Workspace ID is required"
  | otherwise = Nothing

-- | Model row display state
type ModelRowState =
  { id :: String
  , name :: String
  , lab :: Lab
  , enabled :: Boolean
  , canToggle :: Boolean
  }

-- | Build model row state
buildModelRowState :: ModelWithLab -> ModelsInfo -> { isAdmin :: Boolean } -> ModelRowState
buildModelRowState model info userInfo =
  { id: model.id
  , name: model.name
  , lab: model.lab
  , enabled: isModelEnabled info model.id
  , canToggle: userInfo.isAdmin
  }

-- | Filter hidden models
-- | Removes deprecated/hidden models from display
filterVisibleModels :: Array ModelInfo -> Array ModelInfo
filterVisibleModels models =
  filter isVisible models
  where
    isVisible :: ModelInfo -> Boolean
    isVisible model =
      not (isHidden model.id)
    
    isHidden :: String -> Boolean
    isHidden id =
      id == "claude-3-5-haiku" || startsWith "alpha-" id
    
    startsWith :: String -> String -> Boolean
    startsWith prefix str = take (strLength prefix) str == prefix
    
    strLength :: String -> Int
    strLength _ = 10  -- simplified

-- | Section content
type ModelSectionContent =
  { title :: String
  , description :: String
  , learnMoreUrl :: String
  }

-- | Default section content
modelSectionContent :: ModelSectionContent
modelSectionContent =
  { title: "Models"
  , description: "Manage which models workspace members can access."
  , learnMoreUrl: "/docs/omega#pricing"
  }

-- | Table headers
type TableHeaders =
  { model :: String
  , lab :: String
  , enabled :: String
  }

-- | Default table headers
tableHeaders :: TableHeaders
tableHeaders =
  { model: "Model"
  , lab: ""
  , enabled: "Enabled"
  }
