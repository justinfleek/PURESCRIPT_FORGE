-- | ProviderIcon Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/provider-icon.tsx (25 lines)
-- |
-- | AI provider icon using SVG sprite.
-- | Pure Halogen implementation.
-- |
-- | Data Attributes:
-- | - `data-component="provider-icon"` - SVG element
module UI.Components.ProviderIcon
  ( component
  , Input
  , ProviderIconId
  , defaultInput
  , allProviderIds
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

-- | Type alias for provider icon ID
type ProviderIconId = String

-- | ProviderIcon input props
type Input =
  { id :: ProviderIconId   -- Provider ID (openai, anthropic, google, etc.)
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { id: "openai"
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
  HH.element (HH.ElemName "svg")
    ([ HP.attr (HH.AttrName "data-component") "provider-icon"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "aria-hidden") "true"
    ] <> classAttr state.input.className)
    [ renderProviderPath state.input.id ]

-- | Render the appropriate SVG content for each provider
-- | Pure function mapping provider IDs to SVG elements
renderProviderPath :: forall w i. ProviderIconId -> HH.HTML w i
renderProviderPath providerId = case providerId of
  "openai" -> 
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M22.282 9.821a5.985 5.985 0 0 0-.516-4.91 6.046 6.046 0 0 0-6.51-2.9A6.065 6.065 0 0 0 4.981 4.18a5.985 5.985 0 0 0-3.998 2.9 6.046 6.046 0 0 0 .743 7.097 5.98 5.98 0 0 0 .51 4.911 6.051 6.051 0 0 0 6.515 2.9A5.985 5.985 0 0 0 13.26 24a6.056 6.056 0 0 0 5.772-4.206 5.99 5.99 0 0 0 3.997-2.9 6.056 6.056 0 0 0-.747-7.073zM13.26 22.43a4.476 4.476 0 0 1-2.876-1.04l.141-.081 4.779-2.758a.795.795 0 0 0 .392-.681v-6.737l2.02 1.168a.071.071 0 0 1 .038.052v5.583a4.504 4.504 0 0 1-4.494 4.494zM3.6 18.304a4.47 4.47 0 0 1-.535-3.014l.142.085 4.783 2.759a.771.771 0 0 0 .78 0l5.843-3.369v2.332a.08.08 0 0 1-.033.062L9.74 19.95a4.5 4.5 0 0 1-6.14-1.646zM2.34 7.896a4.485 4.485 0 0 1 2.366-1.973V11.6a.766.766 0 0 0 .388.677l5.815 3.355-2.02 1.168a.076.076 0 0 1-.071 0l-4.83-2.786A4.504 4.504 0 0 1 2.34 7.896zm16.597 3.855l-5.833-3.387L15.119 7.2a.076.076 0 0 1 .071 0l4.83 2.791a4.494 4.494 0 0 1-.676 8.105v-5.678a.79.79 0 0 0-.407-.667zm2.01-3.023l-.141-.085-4.774-2.782a.776.776 0 0 0-.785 0L9.409 9.23V6.897a.066.066 0 0 1 .028-.061l4.83-2.787a4.5 4.5 0 0 1 6.68 4.66zm-12.64 4.135l-2.02-1.164a.08.08 0 0 1-.038-.057V6.075a4.5 4.5 0 0 1 7.375-3.453l-.142.08L8.704 5.46a.795.795 0 0 0-.393.681zm1.097-2.365l2.602-1.5 2.607 1.5v2.999l-2.597 1.5-2.607-1.5z"
      , HP.attr (HH.AttrName "fill") "currentColor"
      ] []
  
  "anthropic" ->
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M17.304 3.541h-3.672l6.696 16.918h3.672zm-10.608 0L0 20.459h3.744l1.368-3.552h7.032l1.368 3.552h3.744L10.56 3.541zm-.072 10.44l2.376-6.168 2.376 6.168z"
      , HP.attr (HH.AttrName "fill") "currentColor"
      ] []
  
  "google" ->
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M12.48 10.92v3.28h7.84c-.24 1.84-.853 3.187-1.8 4.133-1.147 1.147-2.933 2.4-6.04 2.4-4.813 0-8.587-3.893-8.587-8.707s3.774-8.707 8.587-8.707c2.6 0 4.507 1.027 5.907 2.347l2.307-2.307C18.747 1.44 16.133 0 12.48 0 5.867 0 .307 5.387.307 12s5.56 12 12.173 12c3.573 0 6.267-1.173 8.373-3.36 2.16-2.16 2.84-5.213 2.84-7.667 0-.76-.053-1.467-.173-2.053z"
      , HP.attr (HH.AttrName "fill") "currentColor"
      ] []
  
  "azure" ->
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M13.05.001L5.957 7.587.164 18.49h5.786zm.877.72l-3.235 8.506 4.71 5.774L5.87 23.28h17.966z"
      , HP.attr (HH.AttrName "fill") "currentColor"
      ] []
  
  "aws" ->
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M6.763 10.036c0 .296.032.535.088.71.064.176.144.368.256.576.04.063.056.127.056.183 0 .08-.048.16-.152.24l-.503.335a.383.383 0 01-.208.072c-.08 0-.16-.04-.239-.112a2.47 2.47 0 01-.287-.375 6.18 6.18 0 01-.248-.471c-.622.734-1.405 1.101-2.347 1.101-.67 0-1.205-.191-1.596-.574-.392-.382-.591-.894-.591-1.536 0-.678.239-1.23.726-1.644.487-.415 1.133-.622 1.955-.622.272 0 .551.024.846.064.296.04.6.104.918.176v-.583c0-.607-.127-1.03-.375-1.277-.255-.248-.686-.367-1.3-.367-.28 0-.567.032-.863.104a6.37 6.37 0 00-.863.279c-.128.056-.224.088-.28.096a.49.49 0 01-.127.024c-.112 0-.168-.08-.168-.247v-.391c0-.128.016-.224.056-.28a.597.597 0 01.224-.167c.28-.144.614-.263 1.005-.36a4.84 4.84 0 011.246-.151c.95 0 1.644.215 2.091.647.439.43.663 1.085.663 1.963v2.586zm-3.24 1.214c.263 0 .534-.048.822-.144.287-.096.543-.271.75-.518.128-.152.224-.32.272-.512.047-.191.08-.423.08-.694v-.335a6.66 6.66 0 00-.735-.136 6.02 6.02 0 00-.75-.048c-.535 0-.926.104-1.19.32-.263.215-.39.518-.39.917 0 .375.095.655.295.846.191.2.47.304.846.304zm6.404.967c-.144 0-.24-.024-.304-.08-.064-.048-.12-.16-.168-.311L7.586 5.55a1.398 1.398 0 01-.072-.343c0-.136.068-.21.204-.21h.782c.152 0 .256.024.312.08.064.048.112.16.16.311l1.342 5.284 1.245-5.284c.04-.16.088-.263.152-.311a.549.549 0 01.32-.08h.638c.152 0 .256.024.32.08.063.048.12.16.151.311l1.261 5.348 1.381-5.348c.048-.16.104-.263.16-.311a.52.52 0 01.311-.08h.743c.136 0 .212.068.212.21 0 .04-.008.08-.016.128a1.137 1.137 0 01-.056.215l-1.924 6.17c-.048.16-.104.263-.168.311a.508.508 0 01-.303.08h-.687c-.151 0-.255-.024-.319-.08-.063-.056-.119-.16-.151-.32l-1.238-5.148-1.23 5.14c-.04.16-.088.264-.152.32-.063.056-.175.08-.327.08zm10.256.215c-.415 0-.83-.048-1.229-.143-.399-.096-.71-.2-.918-.32-.128-.071-.215-.151-.247-.223a.563.563 0 01-.048-.224v-.407c0-.167.064-.247.183-.247.048 0 .096.008.144.024.048.016.12.048.2.08.271.12.566.215.878.279.319.064.63.096.95.096.502 0 .894-.088 1.165-.264a.86.86 0 00.415-.758.777.777 0 00-.215-.559c-.144-.151-.415-.287-.806-.415l-1.157-.359c-.583-.183-1.014-.454-1.277-.806a1.856 1.856 0 01-.391-1.133c0-.327.072-.615.215-.862.144-.248.335-.464.575-.632.24-.176.51-.304.83-.391.32-.088.655-.136 1.006-.136.175 0 .359.008.535.032.183.024.35.056.518.088.16.04.312.08.455.127.144.048.256.096.336.144.12.064.208.128.263.2a.437.437 0 01.072.247v.375c0 .168-.064.256-.184.256a.828.828 0 01-.303-.096 3.652 3.652 0 00-1.532-.311c-.455 0-.815.072-1.062.223-.248.152-.375.383-.375.71 0 .224.08.416.24.567.159.152.454.304.877.44l1.134.358c.574.184.99.44 1.237.767.247.327.367.702.367 1.117 0 .335-.064.64-.191.905a2.043 2.043 0 01-.551.71c-.24.2-.527.35-.862.455-.336.12-.71.176-1.126.176z"
      , HP.attr (HH.AttrName "fill") "currentColor"
      ] []
  
  "mistral" ->
    HH.element (HH.ElemName "rect")
      [ HP.attr (HH.AttrName "x") "4"
      , HP.attr (HH.AttrName "y") "4"
      , HP.attr (HH.AttrName "width") "16"
      , HP.attr (HH.AttrName "height") "16"
      , HP.attr (HH.AttrName "fill") "currentColor"
      ] []
  
  "cohere" ->
    HH.element (HH.ElemName "circle")
      [ HP.attr (HH.AttrName "cx") "12"
      , HP.attr (HH.AttrName "cy") "12"
      , HP.attr (HH.AttrName "r") "10"
      , HP.attr (HH.AttrName "fill") "currentColor"
      ] []
  
  -- Default: render a generic AI icon placeholder
  _ ->
    HH.element (HH.ElemName "path")
      [ HP.attr (HH.AttrName "d") "M12 2L2 7l10 5 10-5-10-5zM2 17l10 5 10-5M2 12l10 5 10-5"
      , HP.attr (HH.AttrName "stroke") "currentColor"
      , HP.attr (HH.AttrName "fill") "none"
      , HP.attr (HH.AttrName "stroke-width") "2"
      ] []

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROVIDER IDS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | List of all available provider icon IDs
allProviderIds :: Array ProviderIconId
allProviderIds =
  [ "openai"
  , "anthropic"
  , "google"
  , "azure"
  , "aws"
  , "mistral"
  , "cohere"
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- NO FFI NEEDED
-- ═══════════════════════════════════════════════════════════════════════════════
-- This component uses only standard Halogen/Web APIs.
-- SVG icons are rendered as pure Halogen HTML.
-- No external sprite file needed - paths embedded directly.
