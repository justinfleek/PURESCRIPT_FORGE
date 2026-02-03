-- | Icon Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/icon.tsx (108 lines)
-- |
-- | SVG icon component with comprehensive icon library.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | All icons render at 20x20 viewbox.
-- |
-- | Data Attributes:
-- | - `data-component="icon"` - Root wrapper div
-- | - `data-size="small|normal|medium|large"` - Size variant
-- | - `data-slot="icon-svg"` - The SVG element
module UI.Components.Icon
  ( component
  , Input
  , IconName
  , IconSize(..)
  , defaultInput
  , allIconNames
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Icon size variants
data IconSize
  = Small
  | Normal
  | Medium
  | Large

derive instance eqIconSize :: Eq IconSize

sizeToString :: IconSize -> String
sizeToString Small = "small"
sizeToString Normal = "normal"
sizeToString Medium = "medium"
sizeToString Large = "large"

-- | Type alias for icon name
type IconName = String

-- | Icon input props
type Input =
  { name :: IconName
  , size :: IconSize
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { name: "check"
  , size: Normal
  , className: Nothing
  }

-- | Internal state (stateless component)
type State = { input :: Input }

-- | Internal actions
data Action = Receive Input

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPONENT
-- ═══════════════════════════════════════════════════════════════════════════════

component :: forall q o m. MonadAff m => H.Component q Input o m
component = H.mkComponent
  { initialState: \input -> { input }
  , render
  , eval: H.mkEval $ H.defaultEval
      { receive = Just <<< Receive
      }
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    ([ HP.attr (HH.AttrName "data-component") "icon"
    , HP.attr (HH.AttrName "data-size") (sizeToString state.input.size)
    ] <> classAttr state.input.className)
    [ renderSvg state.input.name ]

renderSvg :: forall w i. IconName -> HH.HTML w i
renderSvg name =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "data-slot") "icon-svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 20 20"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "aria-hidden") "true"
    ]
    [ renderIconPath name ]

-- | Render the appropriate path for each icon
-- | This is a pure function mapping icon names to SVG paths
renderIconPath :: forall w i. IconName -> HH.HTML w i
renderIconPath name = case name of
  "check" -> 
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M5 11.9657L8.37838 14.7529L15 5.83398"
      , HP.attr (HH.AttrName "stroke") "currentColor"
      , HP.attr (HH.AttrName "stroke-linecap") "square"
      ] []
  "close" ->
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M3.75 3.75L16.25 16.25M16.25 3.75L3.75 16.25"
      , HP.attr (HH.AttrName "stroke") "currentColor"
      , HP.attr (HH.AttrName "stroke-linecap") "square"
      ] []
  "chevron-down" ->
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M6.6665 8.33325L9.99984 11.6666L13.3332 8.33325"
      , HP.attr (HH.AttrName "stroke") "currentColor"
      , HP.attr (HH.AttrName "stroke-linecap") "square"
      ] []
  "chevron-right" ->
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M8.33301 13.3327L11.6663 9.99935L8.33301 6.66602"
      , HP.attr (HH.AttrName "stroke") "currentColor"
      , HP.attr (HH.AttrName "stroke-linecap") "square"
      ] []
  "plus" ->
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M9.9987 2.20703V9.9987M9.9987 9.9987V17.7904M9.9987 9.9987H2.20703M9.9987 9.9987H17.7904"
      , HP.attr (HH.AttrName "stroke") "currentColor"
      , HP.attr (HH.AttrName "stroke-linecap") "square"
      ] []
  "magnifying-glass" ->
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M15.8332 15.8337L13.0819 13.0824M14.6143 9.39088C14.6143 12.2759 12.2755 14.6148 9.39039 14.6148C6.50532 14.6148 4.1665 12.2759 4.1665 9.39088C4.1665 6.5058 6.50532 4.16699 9.39039 4.16699C12.2755 4.16699 14.6143 6.5058 14.6143 9.39088Z"
      , HP.attr (HH.AttrName "stroke") "currentColor"
      , HP.attr (HH.AttrName "stroke-linecap") "square"
      ] []
  "settings-gear" ->
    HH.element (HH.ElemName "g") []
      [ HH.element (HH.ElemName "path")
          [ HP.attr (HH.AttrName "d") "M7.62516 4.46094L5.05225 3.86719L3.86475 5.05469L4.4585 7.6276L2.0835 9.21094V10.7943L4.4585 12.3776L3.86475 14.9505L5.05225 16.138L7.62516 15.5443L9.2085 17.9193H10.7918L12.3752 15.5443L14.9481 16.138L16.1356 14.9505L15.5418 12.3776L17.9168 10.7943V9.21094L15.5418 7.6276L16.1356 5.05469L14.9481 3.86719L12.3752 4.46094L10.7918 2.08594H9.2085L7.62516 4.46094Z"
          , HP.attr (HH.AttrName "stroke") "currentColor"
          ] []
      , HH.element (HH.ElemName "path")
          [ HP.attr (HH.AttrName "d") "M12.5002 10.0026C12.5002 11.3833 11.3809 12.5026 10.0002 12.5026C8.61945 12.5026 7.50016 11.3833 7.50016 10.0026C7.50016 8.62189 8.61945 7.5026 10.0002 7.5026C11.3809 7.5026 12.5002 8.62189 12.5002 10.0026Z"
          , HP.attr (HH.AttrName "stroke") "currentColor"
          ] []
      ]
  "trash" ->
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M4.58342 17.9134L4.58369 17.4134L4.22787 17.5384L4.22766 18.0384H4.58342V17.9134ZM15.4167 17.9134V18.0384H15.7725L15.7723 17.5384L15.4167 17.9134ZM2.08342 3.95508V3.45508H1.58342V3.95508H2.08342V4.45508V3.95508ZM17.9167 4.45508V4.95508H18.4167V4.45508H17.9167V3.95508V4.45508ZM4.16677 4.58008L3.66701 4.5996L4.22816 17.5379L4.72792 17.4934L5.22767 17.4489L4.66652 4.54055L4.16677 4.58008ZM4.58342 18.0384V17.9134H15.4167V18.0384V18.5384H4.58342V18.0384ZM15.4167 17.9134L15.8332 17.5379L16.2498 4.5996L15.7501 4.58008L15.2503 4.56055L14.8337 17.4989L15.4167 17.9134ZM15.8334 4.58008V4.08008H4.16677V4.58008V5.08008H15.8334V4.58008ZM2.08342 4.45508V4.95508H4.16677V4.58008V4.08008H2.08342V4.45508ZM15.8334 4.58008V5.08008H17.9167V4.45508V3.95508H15.8334V4.58008ZM6.83951 4.35149L7.432 4.55047C7.79251 3.47701 8.80699 2.70508 10.0001 2.70508V2.20508V1.70508C8.25392 1.70508 6.77335 2.83539 6.24702 4.15251L6.83951 4.35149ZM10.0001 2.20508V2.70508C11.1932 2.70508 12.2077 3.47701 12.5682 4.55047L13.1607 4.35149L13.7532 4.15251C13.2269 2.83539 11.7463 1.70508 10.0001 1.70508V2.20508Z"
      , HP.attr (HH.AttrName "fill") "currentColor"
      ] []
  "copy" ->
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M6.2513 6.24935V2.91602H17.0846V13.7493H13.7513M13.7513 6.24935V17.0827H2.91797V6.24935H13.7513Z"
      , HP.attr (HH.AttrName "stroke") "currentColor"
      , HP.attr (HH.AttrName "stroke-linecap") "round"
      ] []
  "edit" ->
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M17.0832 17.0807V17.5807H17.5832V17.0807H17.0832ZM2.9165 17.0807H2.4165V17.5807H2.9165V17.0807ZM2.9165 2.91406V2.41406H2.4165V2.91406H2.9165ZM9.58317 3.41406H10.0832V2.41406H9.58317V2.91406V3.41406ZM17.5832 10.4141V9.91406H16.5832V10.4141H17.0832H17.5832ZM6.24984 11.2474L5.89628 10.8938L5.74984 11.0403V11.2474H6.24984ZM6.24984 13.7474H5.74984V14.2474H6.24984V13.7474ZM8.74984 13.7474V14.2474H8.95694L9.10339 14.101L8.74984 13.7474ZM15.2082 2.28906L15.5617 1.93551L15.2082 1.58196L14.8546 1.93551L15.2082 2.28906ZM17.7082 4.78906L18.0617 5.14262L18.4153 4.78906L18.0617 4.43551L17.7082 4.78906ZM17.0832 17.0807V16.5807H2.9165V17.0807V17.5807H17.0832V17.0807ZM2.9165 17.0807H3.4165V2.91406H2.9165H2.4165V17.0807H2.9165ZM2.9165 2.91406V3.41406H9.58317V2.91406V2.41406H2.9165V2.91406ZM17.0832 10.4141H16.5832V17.0807H17.0832H17.5832V10.4141H17.0832ZM6.24984 11.2474H5.74984V13.7474H6.24984H6.74984V11.2474H6.24984ZM6.24984 13.7474V14.2474H8.74984V13.7474V13.2474H6.24984V13.7474ZM6.24984 11.2474L6.60339 11.6009L15.5617 2.64262L15.2082 2.28906L14.8546 1.93551L5.89628 10.8938L6.24984 11.2474ZM15.2082 2.28906L14.8546 2.64262L17.3546 5.14262L17.7082 4.78906L18.0617 4.43551L15.5617 1.93551L15.2082 2.28906ZM17.7082 4.78906L17.3546 4.43551L8.39628 13.3938L8.74984 13.7474L9.10339 14.101L18.0617 5.14262L17.7082 4.78906Z"
      , HP.attr (HH.AttrName "fill") "currentColor"
      ] []
  "folder" ->
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M2.08301 2.91675V16.2501H17.9163V5.41675H9.99967L8.33301 2.91675H2.08301Z"
      , HP.attr (HH.AttrName "stroke") "currentColor"
      , HP.attr (HH.AttrName "stroke-linecap") "round"
      ] []
  "help" ->
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M7.91683 7.91927V6.2526H12.0835V8.7526L10.0002 10.0026V12.0859M10.0002 13.7526V13.7609M17.9168 10.0026C17.9168 14.3749 14.3724 17.9193 10.0002 17.9193C5.62791 17.9193 2.0835 14.3749 2.0835 10.0026C2.0835 5.63035 5.62791 2.08594 10.0002 2.08594C14.3724 2.08594 17.9168 5.63035 17.9168 10.0026Z"
      , HP.attr (HH.AttrName "stroke") "currentColor"
      , HP.attr (HH.AttrName "stroke-linecap") "square"
      ] []
  "menu" ->
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M2.5 5H17.5M2.5 10H17.5M2.5 15H17.5"
      , HP.attr (HH.AttrName "stroke") "currentColor"
      , HP.attr (HH.AttrName "stroke-linecap") "square"
      ] []
  "download" ->
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M13.9583 10.6257L10 14.584L6.04167 10.6257M10 2.08398V13.959M16.25 17.9173H3.75"
      , HP.attr (HH.AttrName "stroke") "currentColor"
      , HP.attr (HH.AttrName "stroke-linecap") "square"
      ] []
  "stop" ->
    HH.element (HH.ElemName "rect")
      [ HP.attr (HH.AttrName "x") "5"
      , HP.attr (HH.AttrName "y") "5"
      , HP.attr (HH.AttrName "width") "10"
      , HP.attr (HH.AttrName "height") "10"
      , HP.attr (HH.AttrName "fill") "currentColor"
      ] []
  -- Default: render a simple placeholder
  _ ->
    HH.element (HH.ElemName "rect")
      [ HP.attr (HH.AttrName "x") "4"
      , HP.attr (HH.AttrName "y") "4"
      , HP.attr (HH.AttrName "width") "12"
      , HP.attr (HH.AttrName "height") "12"
      , HP.attr (HH.AttrName "stroke") "currentColor"
      , HP.attr (HH.AttrName "fill") "none"
      ] []

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ICON NAMES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | List of all available icon names
allIconNames :: Array IconName
allIconNames =
  [ "check", "close", "chevron-down", "chevron-right", "plus"
  , "magnifying-glass", "settings-gear", "trash", "copy", "edit"
  , "folder", "help", "menu", "download", "stop"
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only standard Halogen/Web APIs.
-- SVG icons are rendered as pure Halogen HTML.
