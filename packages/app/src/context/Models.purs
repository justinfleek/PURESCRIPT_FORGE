-- | Models context - manages AI model selection and visibility
-- | Migrated from: forge-dev/packages/app/src/context/models.tsx
module Sidepanel.Context.Models
  ( ModelKey
  , Visibility(..)
  , UserModel
  , ModelsStore
  , mkModelsStore
  , modelKeyStr
  , isVisible
  , setVisibility
  , pushRecent
  , getVariant
  , setVariant
  ) where

import Prelude

import Data.Array (filter, findIndex, length, snoc, take)
import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)

-- | Model identifier
type ModelKey =
  { providerID :: String
  , modelID :: String
  }

-- | Model visibility state
data Visibility
  = Show
  | Hide

derive instance eqVisibility :: Eq Visibility

instance showVisibility :: Show Visibility where
  show Show = "show"
  show Hide = "hide"

-- | User model preferences
type UserModel =
  { providerID :: String
  , modelID :: String
  , visibility :: Visibility
  , favorite :: Maybe Boolean
  }

-- | Models store state
type ModelsStore =
  { user :: Array UserModel
  , recent :: Array ModelKey
  , variant :: Map String (Maybe String)
  }

-- | Create initial models store
mkModelsStore :: ModelsStore
mkModelsStore =
  { user: []
  , recent: []
  , variant: Map.empty
  }

-- | Convert model key to string
modelKeyStr :: ModelKey -> String
modelKeyStr key = key.providerID <> ":" <> key.modelID

-- | Check if a model is visible
isVisible :: ModelsStore -> ModelKey -> Boolean -> Boolean
isVisible store model isLatest =
  let
    matching = filter (\u -> u.providerID == model.providerID && u.modelID == model.modelID) store.user
    userPref = case Array.head matching of
      Nothing -> Nothing
      Just x -> Just x.visibility
  in
    case userPref of
      Just Hide -> false
      Just Show -> true
      Nothing -> isLatest

-- | Set model visibility
setVisibility :: ModelsStore -> ModelKey -> Boolean -> ModelsStore
setVisibility store model visible =
  let
    state = if visible then Show else Hide
    idx = findIndex (\u -> u.providerID == model.providerID && u.modelID == model.modelID) store.user
  in
    case idx of
      Just i ->
        -- Update existing
        store { user = updateAt i (\u -> u { visibility = state }) store.user }
      Nothing ->
        -- Add new
        store { user = snoc store.user { providerID: model.providerID, modelID: model.modelID, visibility: state, favorite: Nothing } }
  where
    updateAt :: forall a. Int -> (a -> a) -> Array a -> Array a
    updateAt index f arr =
      let before = take index arr
          after = Array.drop index arr
      in case Array.uncons after of
          Nothing -> arr
          Just { head: x, tail: rest } -> before <> Array.cons (f x) rest

-- | Push model to recent list
pushRecent :: ModelsStore -> ModelKey -> ModelsStore
pushRecent store model =
  let
    -- Remove existing if present
    filtered = filter (\m -> not (m.providerID == model.providerID && m.modelID == model.modelID)) store.recent
    -- Add to front
    newRecent = Array.cons model filtered
    -- Keep max 5
    trimmed = take 5 newRecent
  in
    store { recent = trimmed }

-- | Get variant for a model
variantKey :: ModelKey -> String
variantKey model = model.providerID <> "/" <> model.modelID

getVariant :: ModelsStore -> ModelKey -> Maybe String
getVariant store model =
  case Map.lookup (variantKey model) store.variant of
    Nothing -> Nothing
    Just v -> v

-- | Set variant for a model
setVariant :: ModelsStore -> ModelKey -> Maybe String -> ModelsStore
setVariant store model value =
  store { variant = Map.insert (variantKey model) value store.variant }
