-- | FileContextView Render Functions
-- |
-- | Rendering functions for the file context view component.
-- |
-- | Coeffect Equation:
-- |   Render : State -> H.ComponentHTML Action () m
-- |   with grouping: DirectoryGroup^n -> View
-- |
-- | Module Coverage: Header, budget bar, file groups, recommendations, preview
module Sidepanel.Components.FileContextView.Render
  ( render
  , renderHeader
  , renderBudgetBar
  , renderFileGroups
  , renderRecommendations
  , renderQuickActions
  , renderPreviewModal
  ) where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Data.Array (filter, mapWithIndex, length, map)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..))
import Data.String as String
import Sidepanel.Components.CodeSelection as CodeSelection
import Sidepanel.Components.FileContextView.Types
  ( State
  , Action(..)
  , FileInContext
  , FileStatus(..)
  , DirectoryGroup
  , ContextBudget
  , detectLanguage
  )

--------------------------------------------------------------------------------
-- | Main Render
--------------------------------------------------------------------------------

-- | Main render function
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "file-context-view") ]
    [ renderHeader state
    , renderBudgetBar state.contextBudget
    , renderFileGroups state.groupedFiles state.selectedFiles
    , renderRecommendations state.files
    , renderQuickActions
    , renderPreviewModal state
    ]

--------------------------------------------------------------------------------
-- | Header
--------------------------------------------------------------------------------

-- | Render header with controls
renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.div
    [ HP.class_ (H.ClassName "file-context-header") ]
    [ HH.h3_ [ HH.text "File Context" ]
    , HH.div
        [ HP.class_ (H.ClassName "header-controls") ]
        [ HH.input
            [ HP.class_ (H.ClassName "filter-input")
            , HP.type_ HP.InputText
            , HP.placeholder "Filter files..."
            , HP.value state.filterQuery
            , HE.onValueInput UpdateFilter
            ]
        , HH.button
            [ HP.class_ (H.ClassName "btn-refresh")
            , HE.onClick \_ -> RefreshContext
            ]
            [ HH.text "Refresh" ]
        , HH.button
            [ HP.class_ (H.ClassName "btn-clear-all")
            , HE.onClick \_ -> ClearAll
            ]
            [ HH.text "Clear All" ]
        ]
    ]

--------------------------------------------------------------------------------
-- | Budget Bar
--------------------------------------------------------------------------------

-- | Render context budget bar
renderBudgetBar :: forall m. ContextBudget -> H.ComponentHTML Action () m
renderBudgetBar budget =
  HH.div
    [ HP.class_ (H.ClassName "context-budget-bar") ]
    [ HH.div
        [ HP.class_ (H.ClassName "budget-label") ]
        [ HH.text $ "Context Budget: " <> show budget.percentage <> "% (" <> show budget.used <> " / " <> show budget.total <> " tokens)" ]
    , HH.div
        [ HP.class_ (H.ClassName "budget-progress") ]
        [ HH.div
            [ HP.class_ (H.ClassName "budget-fill")
            , HP.style $ "width: " <> show budget.percentage <> "%"
            ]
            []
        ]
    ]

--------------------------------------------------------------------------------
-- | File Groups
--------------------------------------------------------------------------------

-- | Render file groups
renderFileGroups :: forall m. Array DirectoryGroup -> Array String -> H.ComponentHTML Action () m
renderFileGroups groups selected =
  HH.div
    [ HP.class_ (H.ClassName "file-groups") ]
    (mapWithIndex (\index group -> renderDirectoryGroup index group selected) groups)

-- | Render directory group
renderDirectoryGroup :: forall m. Int -> DirectoryGroup -> Array String -> H.ComponentHTML Action () m
renderDirectoryGroup index group selected =
  HH.div
    [ HP.class_ (H.ClassName "directory-group") ]
    [ HH.div
        [ HP.class_ (H.ClassName "directory-header") ]
        [ HH.text $ group.path <> " - " <> show (length group.files) <> " files, " <> show group.totalTokens <> " tokens" ]
    , HH.div
        [ HP.class_ (H.ClassName "directory-files") ]
        (mapWithIndex (\fileIndex file -> renderFile fileIndex file selected) group.files)
    ]

-- | Render file item
renderFile :: forall m. Int -> FileInContext -> Array String -> H.ComponentHTML Action () m
renderFile index file selected =
  let isSelected = Array.elem file.path selected
  in
    HH.div
      [ HP.class_ (H.ClassName $ "file-item " <> if isSelected then "selected" else "")
      , HE.onClick \_ -> ToggleFileSelection file.path
      ]
      [ HH.input
          [ HP.type_ HP.InputCheckbox
          , HP.checked isSelected
          , HE.onChecked \_ -> ToggleFileSelection file.path
          ]
      , HH.span
          [ HP.class_ (H.ClassName "file-icon") ]
          [ HH.text "F" ]
      , HH.span
          [ HP.class_ (H.ClassName "file-path") ]
          [ HH.text file.path ]
      , HH.span
          [ HP.class_ (H.ClassName "file-tokens") ]
          [ HH.text $ show file.tokens <> " tk" ]
      , HH.span
          [ HP.class_ (H.ClassName "file-time") ]
          [ HH.text $ "Read " <> show file.readAt ]
      , HH.button
          [ HP.class_ (H.ClassName "btn-remove")
          , HE.onClick \e -> do
              H.stopPropagation e
              RemoveSelected
          ]
          [ HH.text "-" ]
      , HH.button
          [ HP.class_ (H.ClassName "btn-preview")
          , HE.onClick \e -> do
              H.stopPropagation e
              OpenPreview file.path
          ]
          [ HH.text "E" ]
      ]

--------------------------------------------------------------------------------
-- | Recommendations
--------------------------------------------------------------------------------

-- | Render AI recommendations
renderRecommendations :: forall m. Array FileInContext -> H.ComponentHTML Action () m
renderRecommendations files =
  let recommended = filter (\f -> f.status == Recommended) files
  in
    if length recommended > 0 then
      HH.div
        [ HP.class_ (H.ClassName "recommendations") ]
        [ HH.h4_ [ HH.text "AI Recommendations" ]
        , HH.div
            [ HP.class_ (H.ClassName "recommended-files") ]
            (map renderRecommendedFile recommended)
        ]
    else
      HH.text ""

-- | Render recommended file
renderRecommendedFile :: forall m. FileInContext -> H.ComponentHTML Action () m
renderRecommendedFile file =
  HH.div
    [ HP.class_ (H.ClassName "recommended-file") ]
    [ HH.span
        [ HP.class_ (H.ClassName "recommendation-icon") ]
        [ HH.text "*" ]
    , HH.span
        [ HP.class_ (H.ClassName "recommended-path") ]
        [ HH.text file.path ]
    , HH.span
        [ HP.class_ (H.ClassName "recommended-tokens") ]
        [ HH.text $ "~" <> show file.tokens <> " tk" ]
    , HH.button
        [ HP.class_ (H.ClassName "btn-add")
        , HE.onClick \_ -> AddRecommended file.path
        ]
        [ HH.text "+ Add to Context" ]
    ]

--------------------------------------------------------------------------------
-- | Quick Actions
--------------------------------------------------------------------------------

-- | Render quick actions
renderQuickActions :: forall m. H.ComponentHTML Action () m
renderQuickActions =
  HH.div
    [ HP.class_ (H.ClassName "quick-actions") ]
    [ HH.button
        [ HP.class_ (H.ClassName "btn-add-files") ]
        [ HH.text "+ Add Files..." ]
    , HH.button
        [ HP.class_ (H.ClassName "btn-add-directory") ]
        [ HH.text "D Add Directory..." ]
    , HH.button
        [ HP.class_ (H.ClassName "btn-save-preset") ]
        [ HH.text "S Save as Preset..." ]
    ]

--------------------------------------------------------------------------------
-- | Preview Modal
--------------------------------------------------------------------------------

-- | Render preview modal
renderPreviewModal :: forall m. State -> H.ComponentHTML Action () m
renderPreviewModal state =
  case state.previewFile of
    Just file ->
      HH.div
        [ HP.class_ (H.ClassName "modal-overlay")
        , HE.onClick \_ -> ClosePreview
        ]
        [ HH.div
            [ HP.class_ (H.ClassName "modal modal-large")
            , HE.onClick \e -> H.stopPropagation e
            ]
            [ HH.div
                [ HP.class_ (H.ClassName "modal-header") ]
                [ HH.h3_ [ HH.text $ "Preview: " <> file ]
                , HH.button
                    [ HP.class_ (H.ClassName "btn-close")
                    , HE.onClick \_ -> ClosePreview
                    ]
                    [ HH.text "x" ]
                ]
            , HH.div
                [ HP.class_ (H.ClassName "modal-body") ]
                [ case state.previewContent of
                    Just content ->
                      let
                        lines = String.split (Pattern "\n") content
                        language = detectLanguage file
                      in
                        HH.slot (H.Slot unit) unit CodeSelection.component
                          { codeLines: lines
                          , filePath: Just file
                          , language: language
                          }
                          (case _ of
                            CodeSelection.Copied code -> HandleCodeCopied code
                            CodeSelection.AddedToChat code -> HandleCodeAddedToChat code
                            CodeSelection.SelectionChanged _ -> NoOp)
                    Nothing ->
                      HH.text "Loading..."
                ]
            , HH.div
                [ HP.class_ (H.ClassName "modal-footer") ]
                [ HH.button
                    [ HP.class_ (H.ClassName "btn btn-primary")
                    , HE.onClick \_ -> ClosePreview
                    ]
                    [ HH.text "Close" ]
                ]
            ]
        ]
    Nothing ->
      HH.text ""
