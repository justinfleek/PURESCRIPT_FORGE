-- | FileContextView Handler
-- |
-- | Action handling for the file context view component.
-- |
-- | Coeffect Equation:
-- |   Handler : Action -> H.HalogenM State Action () Output m Unit
-- |   with API: WSClient -o Bridge -> Response
-- |
-- | Module Coverage: handleAction, API integration
module Sidepanel.Components.FileContextView.Handler
  ( handleAction
  ) where

import Prelude
import Halogen as H
import Effect.Aff.Class (class MonadAff)
import Data.Array (filter, snoc, map, length)
import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.String (Pattern(..), contains, toLower)
import Sidepanel.Api.Bridge as Bridge
import Sidepanel.Components.FileContextView.Types
  ( State
  , Action(..)
  , Output(..)
  , groupFilesByDirectory
  , calculateBudget
  )

--------------------------------------------------------------------------------
-- | Action Handler
--------------------------------------------------------------------------------

-- | Handle component actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    state <- H.get
    case state.wsClient of
      Just client -> do
        result <- H.liftAff $ Bridge.listFilesInContext client { sessionId: Nothing, filter: Nothing }
        case result of
          Right response -> do
            H.modify_ \s -> s
              { files = response.files
              , groupedFiles = groupFilesByDirectory response.files
              , contextBudget =
                  { used: response.contextBudget.used
                  , total: response.contextBudget.total
                  , percentage: if response.contextBudget.total > 0
                      then (Int.toNumber response.contextBudget.used / Int.toNumber response.contextBudget.total) * 100.0
                      else 0.0
                  }
              }
          Left _ -> pure unit
      Nothing -> pure unit
  
  UpdateFiles files -> do
    H.modify_ \s -> s
      { files = files
      , groupedFiles = groupFilesByDirectory files
      , contextBudget = calculateBudget files s.contextBudget.total
      }
  
  ToggleFileSelection path -> do
    state <- H.get
    let newSelected = if Array.elem path state.selectedFiles then
          filter (\p -> p /= path) state.selectedFiles
        else
          snoc state.selectedFiles path
    H.modify_ \s -> s { selectedFiles = newSelected }
  
  SelectAll -> do
    state <- H.get
    let allPaths = map _.path state.files
    H.modify_ \s -> s { selectedFiles = allPaths }
  
  DeselectAll -> do
    H.modify_ \s -> s { selectedFiles = [] }
  
  RemoveSelected -> do
    state <- H.get
    if length state.selectedFiles > 0 then do
      H.raise (FilesRemoved state.selectedFiles)
      H.modify_ \s -> s
        { files = filter (\f -> not $ Array.elem f.path state.selectedFiles) s.files
        , selectedFiles = []
        }
      updatedState <- H.get
      H.modify_ \s -> s
        { groupedFiles = groupFilesByDirectory updatedState.files
        , contextBudget = calculateBudget updatedState.files s.contextBudget.total
        }
    else
      pure unit
  
  AddRecommended path -> do
    state <- H.get
    case state.wsClient of
      Just client -> do
        result <- H.liftAff $ Bridge.addFileToContext client { path, sessionId: Nothing }
        case result of
          Right response -> do
            H.raise (FilesAdded [path])
            H.modify_ \s -> s
              { contextBudget =
                  { used: response.contextBudget.used
                  , total: response.contextBudget.total
                  , percentage: if response.contextBudget.total > 0
                      then (Int.toNumber response.contextBudget.used / Int.toNumber response.contextBudget.total) * 100.0
                      else 0.0
                  }
              }
          Left err -> pure unit
      Nothing -> pure unit
  
  UpdateFilter query -> do
    H.modify_ \s -> s { filterQuery = query }
    state <- H.get
    let filtered = if query == "" then
          state.files
        else
          filter (\f -> contains (Pattern $ toLower query) (toLower f.path)) state.files
    H.modify_ \s -> s { groupedFiles = groupFilesByDirectory filtered }
  
  ToggleShowStale -> do
    H.modify_ \s -> s { showStale = not s.showStale }
  
  ToggleShowRecommended -> do
    H.modify_ \s -> s { showRecommended = not s.showRecommended }
  
  RefreshContext -> do
    state <- H.get
    case state.wsClient of
      Just client -> do
        result <- H.liftAff $ Bridge.listFilesInContext client { sessionId: Nothing, filter: Nothing }
        case result of
          Right response -> do
            H.raise ContextRefreshed
            H.modify_ \s -> s
              { files = response.files
              , groupedFiles = groupFilesByDirectory response.files
              , contextBudget =
                  { used: response.contextBudget.used
                  , total: response.contextBudget.total
                  , percentage: if response.contextBudget.total > 0
                      then (Int.toNumber response.contextBudget.used / Int.toNumber response.contextBudget.total) * 100.0
                      else 0.0
                  }
              }
          Left err -> pure unit
      Nothing -> pure unit
  
  ClearAll -> do
    state <- H.get
    let allPaths = map _.path state.files
    H.raise (FilesRemoved allPaths)
    H.modify_ \s -> s
      { files = []
      , groupedFiles = []
      , selectedFiles = []
      , contextBudget = s.contextBudget { used = 0, percentage = 0.0 }
      }
  
  OpenPreview file -> do
    state <- H.get
    case state.wsClient of
      Just client -> do
        result <- H.liftAff $ Bridge.readFileContent client { path: file }
        case result of
          Right response -> do
            H.modify_ \s -> s { previewFile = Just file, previewContent = response.content }
          Left err -> do
            H.modify_ \s -> s { previewFile = Just file, previewContent = Just ("Error loading file: " <> err.message) }
      Nothing -> do
        H.modify_ \s -> s { previewFile = Just file, previewContent = Just "Not connected to bridge server" }
  
  ClosePreview -> do
    H.modify_ \s -> s { previewFile = Nothing, previewContent = Nothing }
  
  HandleCodeCopied code -> pure unit
  
  HandleCodeAddedToChat code -> pure unit
  
  NoOp -> pure unit
