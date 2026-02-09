module Nexus.NetworkVisualization where

import Prelude

import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff)
import Data.Array as Array
import Data.Maybe (Maybe(..))

type Node = 
  { id :: String
  , label :: String
  , nodeType :: String
  , x :: Number
  , y :: Number
  }

type Edge = 
  { id :: String
  , sourceId :: String
  , targetId :: String
  , weight :: Number
  }

type State = 
  { nodes :: Array Node
  , edges :: Array Edge
  , selectedNode :: Maybe String
  , zoom :: Number
  }

data Action
  = Initialize
  | SelectNode String
  | ZoomIn
  | ZoomOut
  | Pan Number Number

component :: forall q i o m. MonadAff m => H.Component q i o m
component = H.mkComponent
  { initialState: \_ -> 
      { nodes: []
      , edges: []
      , selectedNode: Nothing
      , zoom: 1.0
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state = 
  HH.div
    [ HP.class_ (HH.ClassName "nexus-network-visualization") ]
    [ HH.div
        [ HP.class_ (HH.ClassName "network-controls") ]
        [ HH.button
            [ HP.class_ (HH.ClassName "zoom-in")
            , HE.onClick \_ -> ZoomIn
            ]
            [ HH.text "+" ]
        , HH.button
            [ HP.class_ (HH.ClassName "zoom-out")
            , HE.onClick \_ -> ZoomOut
            ]
            [ HH.text "-" ]
        ]
    , HH.svg
        [ HP.class_ (HH.ClassName "network-graph")
        , HP.width 800
        , HP.height 600
        ]
        [ HH.g
            [ HP.class_ (HH.ClassName "edges") ]
            (Array.map renderEdge state.edges)
        , HH.g
            [ HP.class_ (HH.ClassName "nodes") ]
            (Array.map (renderNode state.selectedNode) state.nodes)
        ]
    ]

renderEdge :: forall m. Edge -> H.ComponentHTML Action () m
renderEdge edge =
  HH.line
    [ HP.x1 0.0
    , HP.y1 0.0
    , HP.x2 0.0
    , HP.y2 0.0
    , HP.class_ (HH.ClassName "edge")
    , HP.strokeWidth edge.weight
    ]
    []

renderNode :: forall m. Maybe String -> Node -> H.ComponentHTML Action () m
renderNode selectedNodeId node =
  HH.circle
    [ HP.cx node.x
    , HP.cy node.y
    , HP.r 10.0
    , HP.class_ (HH.ClassName ("node " <> node.nodeType))
    , HE.onClick \_ -> SelectNode node.id
    ]
    []

handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action () o m Unit
handleAction = case _ of
  Initialize -> do
    -- TODO: Load network graph from Bridge Server
    pure unit
  SelectNode nodeId -> do
    H.modify_ _ { selectedNode = Just nodeId }
  ZoomIn -> do
    H.modify_ \s -> s { zoom = s.zoom + 0.1 }
  ZoomOut -> do
    H.modify_ \s -> s { zoom = max 0.1 (s.zoom - 0.1) }
  Pan dx dy -> do
    -- TODO: Implement panning
    pure unit
