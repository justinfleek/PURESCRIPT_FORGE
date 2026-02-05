{-|
Module      : Sidepanel.Theme.ThemeProvider
Description : Theme provider component for global theme management

Halogen component that provides theme configuration and editing capabilities.
-}
module Sidepanel.Theme.ThemeProvider where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Sidepanel.Theme.ModernTheme as ModernTheme
import Effect.Class (liftEffect)

-- | Component state
type State =
  { theme :: ModernTheme.ThemeConfig
  , isEditing :: Boolean
  }

-- | Component actions
data Action
  = Initialize
  | ToggleEditMode
  | UpdateColor String String  -- colorVar, value
  | UpdateSpacing String String  -- spacingVar, value
  | UpdateTypography String String  -- typographyVar, value
  | UpdateEffects String String  -- effectsVar, value
  | ResetTheme

-- | Component output
data Output
  = ThemeChanged ModernTheme.ThemeConfig

-- | Component input
type Input = Unit

-- | Component factory
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  {   initialState: \_ ->
      { theme: ModernTheme.defaultThemeConfig
      , isEditing: false
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

-- | Render component
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "theme-provider") ]
    [ if state.isEditing then
        renderThemeEditor state.theme
      else
        HH.text ""
    ]

-- | Render theme editor
renderThemeEditor :: forall m. ModernTheme.ThemeConfig -> H.ComponentHTML Action () m
renderThemeEditor theme =
  HH.div
    [ HP.class_ (H.ClassName "theme-editor theme-card") ]
    [ HH.h3
        [ HP.class_ (H.ClassName "theme-card-title") ]
        [ HH.text "Theme Editor" ]
    , renderColorEditor theme.colors
    , renderSpacingEditor theme.spacing
    , renderTypographyEditor theme.typography
    , renderEffectsEditor theme.effects
    , HH.button
        [ HP.class_ (H.ClassName "theme-button")
        , HE.onClick \_ -> ResetTheme
        ]
        [ HH.text "Reset to Default" ]
    ]

-- | Render color editor
renderColorEditor :: forall m. _ -> H.ComponentHTML Action () m
renderColorEditor colors =
  HH.div
    [ HP.class_ (H.ClassName "theme-editor-section") ]
    [ HH.h4 [] [ HH.text "Colors" ]
    , renderColorInput "Background" "--theme-bg-primary" colors.background
    , renderColorInput "Card Background" "--theme-bg-card" colors.backgroundCard
    , renderColorInput "Text Primary" "--theme-text-primary" colors.textPrimary
    , renderColorInput "Text Secondary" "--theme-text-secondary" colors.textSecondary
    , renderColorInput "Accent Blue" "--theme-accent-blue" colors.accentBlue
    , renderColorInput "Accent Purple" "--theme-accent-purple" colors.accentPurple
    , renderColorInput "Accent Pink" "--theme-accent-pink" colors.accentPink
    , renderColorInput "Accent Green" "--theme-accent-green" colors.accentGreen
    , renderColorInput "Accent Orange" "--theme-accent-orange" colors.accentOrange
    ]

-- | Render color input
renderColorInput :: forall m. String -> String -> String -> H.ComponentHTML Action () m
renderColorInput label varName value =
  HH.div
    [ HP.class_ (H.ClassName "theme-editor-input-group") ]
    [ HH.label [] [ HH.text label ]
    , HH.input
        [ HP.type_ HP.InputColor
        , HP.value value
        , HE.onValueInput \newValue -> UpdateColor varName newValue
        ]
    , HH.input
        [ HP.type_ HP.InputText
        , HP.value value
        , HE.onValueInput \newValue -> UpdateColor varName newValue
        ]
    ]

-- | Render spacing editor
renderSpacingEditor :: forall m. _ -> H.ComponentHTML Action () m
renderSpacingEditor spacing =
  HH.div
    [ HP.class_ (H.ClassName "theme-editor-section") ]
    [ HH.h4 [] [ HH.text "Spacing" ]
    , renderSpacingInput "Card Padding" "--theme-padding-card" spacing.paddingCard
    , renderSpacingInput "Grid Gap" "--theme-gap-grid" spacing.gapGrid
    , renderSpacingInput "Vertical Gap" "--theme-gap-vertical" spacing.gapVertical
    , renderSpacingInput "Horizontal Gap" "--theme-gap-horizontal" spacing.gapHorizontal
    , renderSpacingInput "Border Radius" "--theme-border-radius" spacing.borderRadius
    ]

-- | Render spacing input
renderSpacingInput :: forall m. String -> String -> String -> H.ComponentHTML Action () m
renderSpacingInput label varName value =
  HH.div
    [ HP.class_ (H.ClassName "theme-editor-input-group") ]
    [ HH.label [] [ HH.text label ]
    , HH.input
        [ HP.type_ HP.InputText
        , HP.value value
        , HE.onValueInput \newValue -> UpdateSpacing varName newValue
        ]
    ]

-- | Render typography editor
renderTypographyEditor :: forall m. _ -> H.ComponentHTML Action () m
renderTypographyEditor typography =
  HH.div
    [ HP.class_ (H.ClassName "theme-editor-section") ]
    [ HH.h4 [] [ HH.text "Typography" ]
    , renderTypographyInput "Font Family" "--theme-font-family" typography.fontFamily
    , renderTypographyInput "Title Size" "--theme-font-size-title" typography.fontSizeTitle
    , renderTypographyInput "Subtitle Size" "--theme-font-size-subtitle" typography.fontSizeSubtitle
    , renderTypographyInput "Card Title Size" "--theme-font-size-card-title" typography.fontSizeCardTitle
    , renderTypographyInput "Card Description Size" "--theme-font-size-card-description" typography.fontSizeCardDescription
    ]

-- | Render typography input
renderTypographyInput :: forall m. String -> String -> String -> H.ComponentHTML Action () m
renderTypographyInput label varName value =
  HH.div
    [ HP.class_ (H.ClassName "theme-editor-input-group") ]
    [ HH.label [] [ HH.text label ]
    , HH.input
        [ HP.type_ HP.InputText
        , HP.value value
        , HE.onValueInput \newValue -> UpdateTypography varName newValue
        ]
    ]

-- | Render effects editor
renderEffectsEditor :: forall m. _ -> H.ComponentHTML Action () m
renderEffectsEditor effects =
  HH.div
    [ HP.class_ (H.ClassName "theme-editor-section") ]
    [ HH.h4 [] [ HH.text "Effects" ]
    , renderEffectsInput "Glow Intensity" "--theme-glow-intensity" effects.glowIntensity
    , renderEffectsInput "Glow Spread" "--theme-glow-spread" effects.glowSpread
    , renderEffectsInput "Shadow Blur" "--theme-shadow-blur" effects.shadowBlur
    , renderEffectsInput "Glow Opacity" "--theme-glow-opacity" effects.glowOpacity
    ]

-- | Render effects input
renderEffectsInput :: forall m. String -> String -> String -> H.ComponentHTML Action () m
renderEffectsInput label varName value =
  HH.div
    [ HP.class_ (H.ClassName "theme-editor-input-group") ]
    [ HH.label [] [ HH.text label ]
    , HH.input
        [ HP.type_ HP.InputText
        , HP.value value
        , HE.onValueInput \newValue -> UpdateEffects varName newValue
        ]
    ]

-- | Handle actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Apply default theme on initialization
    state <- H.get
    liftEffect $ ModernTheme.applyTheme state.theme
  
  ToggleEditMode -> do
    H.modify_ \s -> s { isEditing = not s.isEditing }
  
  UpdateColor varName value -> do
    liftEffect $ ModernTheme.updateThemeColor varName value
    H.modify_ \s -> s
      { theme = updateColorInConfig s.theme varName value
      }
    state <- H.get
    H.raise (ThemeChanged state.theme)
  
  UpdateSpacing varName value -> do
    liftEffect $ ModernTheme.updateThemeSpacing varName value
    H.modify_ \s -> s
      { theme = updateSpacingInConfig s.theme varName value
      }
    state <- H.get
    H.raise (ThemeChanged state.theme)
  
  UpdateTypography varName value -> do
    liftEffect $ ModernTheme.updateThemeTypography varName value
    H.modify_ \s -> s
      { theme = updateTypographyInConfig s.theme varName value
      }
    state <- H.get
    H.raise (ThemeChanged state.theme)
  
  UpdateEffects varName value -> do
    liftEffect $ ModernTheme.updateThemeEffects varName value
    H.modify_ \s -> s
      { theme = updateEffectsInConfig s.theme varName value
      }
    state <- H.get
    H.raise (ThemeChanged state.theme)
  
  ResetTheme -> do
    H.modify_ _ { theme = ModernTheme.defaultThemeConfig }
    liftEffect $ ModernTheme.applyTheme ModernTheme.defaultThemeConfig
    state <- H.get
    H.raise (ThemeChanged state.theme)

-- | Update color in config
updateColorInConfig :: ModernTheme.ThemeConfig -> String -> String -> ModernTheme.ThemeConfig
updateColorInConfig config varName value = case varName of
  "--theme-bg-primary" -> config { colors = config.colors { background = value } }
  "--theme-bg-card" -> config { colors = config.colors { backgroundCard = value } }
  "--theme-text-primary" -> config { colors = config.colors { textPrimary = value } }
  "--theme-text-secondary" -> config { colors = config.colors { textSecondary = value } }
  "--theme-accent-blue" -> config { colors = config.colors { accentBlue = value } }
  "--theme-accent-purple" -> config { colors = config.colors { accentPurple = value } }
  "--theme-accent-pink" -> config { colors = config.colors { accentPink = value } }
  "--theme-accent-green" -> config { colors = config.colors { accentGreen = value } }
  "--theme-accent-orange" -> config { colors = config.colors { accentOrange = value } }
  _ -> config

-- | Update spacing in config
updateSpacingInConfig :: ThemeConfig -> String -> String -> ThemeConfig
updateSpacingInConfig config varName value = case varName of
  "--theme-padding-card" -> config { spacing = config.spacing { paddingCard = value } }
  "--theme-gap-grid" -> config { spacing = config.spacing { gapGrid = value } }
  "--theme-gap-vertical" -> config { spacing = config.spacing { gapVertical = value } }
  "--theme-gap-horizontal" -> config { spacing = config.spacing { gapHorizontal = value } }
  "--theme-border-radius" -> config { spacing = config.spacing { borderRadius = value } }
  _ -> config

-- | Update typography in config
updateTypographyInConfig :: ModernTheme.ThemeConfig -> String -> String -> ModernTheme.ThemeConfig
updateTypographyInConfig config varName value = case varName of
  "--theme-font-family" -> config { typography = config.typography { fontFamily = value } }
  "--theme-font-size-title" -> config { typography = config.typography { fontSizeTitle = value } }
  "--theme-font-size-subtitle" -> config { typography = config.typography { fontSizeSubtitle = value } }
  "--theme-font-size-card-title" -> config { typography = config.typography { fontSizeCardTitle = value } }
  "--theme-font-size-card-description" -> config { typography = config.typography { fontSizeCardDescription = value } }
  _ -> config

-- | Update effects in config
updateEffectsInConfig :: ModernTheme.ThemeConfig -> String -> String -> ModernTheme.ThemeConfig
updateEffectsInConfig config varName value = case varName of
  "--theme-glow-intensity" -> config { effects = config.effects { glowIntensity = value } }
  "--theme-glow-spread" -> config { effects = config.effects { glowSpread = value } }
  "--theme-shadow-blur" -> config { effects = config.effects { shadowBlur = value } }
  "--theme-glow-opacity" -> config { effects = config.effects { glowOpacity = value } }
  _ -> config

