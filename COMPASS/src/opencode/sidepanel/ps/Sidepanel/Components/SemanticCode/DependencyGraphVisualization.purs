{-|
Module      : Sidepanel.Components.SemanticCode.DependencyGraphVisualization
Description : Halogen component for visualizing dependency graphs

Interactive dependency graph visualization with zoom, pan, selection, and circular dependency highlighting.
-}
module Sidepanel.Components.SemanticCode.DependencyGraphVisualization where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Sidepanel.Components.SemanticCode.DependencyGraph
  ( buildDependencyGraph
  , findCircularDependencies
  , findTransitiveDependencies
  )
import Sidepanel.Components.SemanticCode.DependencyGraphTypes
  ( DependencyGraph
  , FileNode
  , DependencyEdge
  , EdgeType(..)
  )

-- | Visual node with position
type VisualNode =
  { node :: FileNode
  , x :: Number
  , y :: Number
  , selected :: Boolean
  , highlighted :: Boolean  -- Part of circular dependency or selected path
  }

-- | Visual edge with calculated positions
type VisualEdge =
  { edge :: DependencyEdge
  , sourceX :: Number
  , sourceY :: Number
  , targetX :: Number
  , targetY :: Number
  , highlighted :: Boolean  -- Part of circular dependency
  }

-- | Component state
type State =
  { graph :: Maybe DependencyGraph
  , visualNodes :: Array VisualNode
  , visualEdges :: Array VisualEdge
  , selectedNode :: Maybe String
  , circularDependencies :: Array (Array String)  -- Cycles in the graph
  , zoom :: Number
  , panX :: Number
  , panY :: Number
  , layout :: LayoutType
  , showCircularOnly :: Boolean  -- Filter to show only circular dependencies
  }

-- | Layout algorithm type
data LayoutType
  = ForceDirected
  | Hierarchical
  | Circular

derive instance eqLayoutType :: Eq LayoutType

-- | Component actions
data Action
  = Initialize
  | LoadGraph DependencyGraph
  | NodeSelected String
  | NodeDeselected
  | ZoomIn
  | ZoomOut
  | Pan Number Number
  | LayoutChanged LayoutType
  | ToggleCircularOnly
  | HighlightPath String  -- Highlight path from selected node

-- | Component output
data Output
  = NodeClicked FileNode
  | EdgeClicked DependencyEdge

-- | Component input
type Input =
  { graph :: Maybe DependencyGraph
  }

-- | Component factory
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \input ->
      { graph: input.graph
      , visualNodes: []
      , visualEdges: []
      , selectedNode: Nothing
      , circularDependencies: []
      , zoom: 1.0
      , panX: 0.0
      , panY: 0.0
      , layout: ForceDirected
      , showCircularOnly: false
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
    [ HP.class_ (H.ClassName "dependency-graph-visualization theme-card") ]
    [ renderControls state
    , renderGraph state
    , renderLegend state
    , renderNodeInfo state.selectedNode state.visualNodes
    ]

-- | Render controls
renderControls :: forall m. State -> H.ComponentHTML Action () m
renderControls state =
  HH.div
    [ HP.class_ (H.ClassName "graph-controls") ]
    [ HH.button
        [ HP.class_ (H.ClassName "zoom-in-btn theme-button")
        , HE.onClick \_ -> ZoomIn
        ]
        [ HH.text "+" ]
    , HH.button
        [ HP.class_ (H.ClassName "zoom-out-btn theme-button")
        , HE.onClick \_ -> ZoomOut
        ]
        [ HH.text "-" ]
    , HH.select
        [ HP.class_ (H.ClassName "layout-select")
        , HE.onValueChange \value ->
            LayoutChanged (case value of
              "hierarchical" -> Hierarchical
              "circular" -> Circular
              _ -> ForceDirected)
        ]
        [ HH.option [ HP.value "force-directed" ] [ HH.text "Force Directed" ]
        , HH.option [ HP.value "hierarchical" ] [ HH.text "Hierarchical" ]
        , HH.option [ HP.value "circular" ] [ HH.text "Circular" ]
        ]
    , HH.label
        [ HP.class_ (H.ClassName "circular-toggle") ]
        [ HH.input
            [ HP.type_ HP.InputCheckbox
            , HP.checked state.showCircularOnly
            , HE.onChecked \_ -> ToggleCircularOnly
            ]
        , HH.text "Show circular dependencies only"
        ]
    , if Array.length state.circularDependencies > 0 then
        HH.div
          [ HP.class_ (H.ClassName "circular-warning") ]
          [ HH.text ("⚠ " <> show (Array.length state.circularDependencies) <> " circular dependencies detected") ]
      else
        HH.text ""
    ]

-- | Render graph SVG
renderGraph :: forall m. State -> H.ComponentHTML Action () m
renderGraph state =
  HH.div
    [ HP.class_ (H.ClassName "graph-container") ]
    [ HH.svg
        [ HP.class_ (H.ClassName "dependency-graph")
        , HP.width 1200
        , HP.height 800
        , HP.viewBox "0 0 1200 800"
        ]
        [ HH.g
            [ HP.class_ (H.ClassName "graph-transform")
            , HP.transform ("translate(" <> show state.panX <> "," <> show state.panY <> ") scale(" <> show state.zoom <> ")")
            ]
            [ HH.g
                [ HP.class_ (H.ClassName "edges") ]
                (Array.map (renderEdge state.selectedNode state.circularDependencies) state.visualEdges)
            , HH.g
                [ HP.class_ (H.ClassName "nodes") ]
                (Array.map (renderNode state.selectedNode state.circularDependencies) state.visualNodes)
            ]
        ]
    ]

-- | Render edge
renderEdge :: forall m. Maybe String -> Array (Array String) -> VisualEdge -> H.ComponentHTML Action () m
renderEdge selectedNodeId circularDeps visualEdge =
  let
    edge = visualEdge.edge
    isCircular = Array.any (\cycle -> Array.elem edge.from cycle && Array.elem edge.to cycle) circularDeps
    isSelected = case selectedNodeId of
      Nothing -> false
      Just selectedId -> edge.from == selectedId || edge.to == selectedId
    edgeClass = "edge " <>
      (if isCircular then "edge-circular " else "") <>
      (if isSelected then "edge-selected " else "") <>
      (case edge.type_ of
        ImportEdge -> "edge-import"
        ExportEdge -> "edge-export"
        CallEdge -> "edge-call"
        TypeEdge -> "edge-type"
        TestEdge -> "edge-test")
    strokeColor = if isCircular then "#ff0000" else if isSelected then "#0066ff" else "#999999"
  in
    HH.g
      [ HP.class_ (H.ClassName edgeClass) ]
      [ HH.line
          [ HP.x1 visualEdge.sourceX
          , HP.y1 visualEdge.sourceY
          , HP.x2 visualEdge.targetX
          , HP.y2 visualEdge.targetY
          , HP.stroke strokeColor
          , HP.strokeWidth (if isCircular then 3.0 else if isSelected then 2.0 else 1.0)
          , HP.strokeDasharray (if isCircular then "5,5" else "none")
          , HE.onClick \_ -> EdgeClicked edge.edge
          ]
          []
      , HH.text
          [ HP.x ((visualEdge.sourceX + visualEdge.targetX) / 2.0)
          , HP.y ((visualEdge.sourceY + visualEdge.targetY) / 2.0)
          , HP.class_ (H.ClassName "edge-label")
          , HP.fontSize "10px"
          , HP.fill "#666666"
          ]
          [ HH.text edge.edge.label ]
      ]

-- | Render node
renderNode :: forall m. Maybe String -> Array (Array String) -> VisualNode -> H.ComponentHTML Action () m
renderNode selectedNodeId circularDeps visualNode =
  let
    node = visualNode.node
    isSelected = case selectedNodeId of
      Nothing -> false
      Just selectedId -> node.id == selectedId
    isCircular = Array.any (\cycle -> Array.elem node.id cycle) circularDeps
    nodeClass = "node " <>
      (if isSelected then "node-selected " else "") <>
      (if isCircular then "node-circular " else "") <>
      ("node-type-" <> node.type_)
    fillColor = if isCircular then "#ff6666" else if isSelected then "#66aaff" else "#cccccc"
    radius = if isSelected then 12.0 else if isCircular then 10.0 else 8.0
  in
    HH.g
      [ HP.class_ (H.ClassName nodeClass) ]
      [ HH.circle
          [ HP.cx visualNode.x
          , HP.cy visualNode.y
          , HP.r radius
          , HP.fill fillColor
          , HP.stroke (if isCircular then "#ff0000" else "#000000")
          , HP.strokeWidth (if isCircular then 2.0 else 1.0)
          , HE.onClick \_ -> NodeSelected node.id
          ]
          []
      , HH.text
          [ HP.x visualNode.x
          , HP.y (visualNode.y + radius + 15.0)
          , HP.class_ (H.ClassName "node-label")
          , HP.textAnchor "middle"
          , HP.fontSize "11px"
          , HP.fill "#000000"
          ]
          [ HH.text node.name ]
      ]

-- | Render legend
renderLegend :: forall m. State -> H.ComponentHTML Action () m
renderLegend state =
  HH.div
    [ HP.class_ (H.ClassName "graph-legend") ]
    [ HH.h4 [] [ HH.text "Legend" ]
    , HH.div
        [ HP.class_ (H.ClassName "legend-item") ]
        [ HH.div
            [ HP.class_ (H.ClassName "legend-color")
            , HP.style "background: #ff6666;"
            ]
            []
        , HH.text "Circular dependency"
        ]
    , HH.div
        [ HP.class_ (H.ClassName "legend-item") ]
        [ HH.div
            [ HP.class_ (H.ClassName "legend-color")
            , HP.style "background: #66aaff;"
            ]
            []
        , HH.text "Selected node"
        ]
    , HH.div
        [ HP.class_ (H.ClassName "legend-item") ]
        [ HH.div
            [ HP.class_ (H.ClassName "legend-color")
            , HP.style "background: #cccccc;"
            ]
            []
        , HH.text "Normal node"
        ]
    , HH.div
        [ HP.class_ (H.ClassName "legend-edge") ]
        [ HH.text "Red dashed = Circular, Blue = Selected path" ]
    ]

-- | Render node info panel
renderNodeInfo :: forall m. Maybe String -> Array VisualNode -> H.ComponentHTML Action () m
renderNodeInfo selectedNodeId visualNodes =
  case selectedNodeId of
    Nothing -> HH.text ""
    Just nodeId -> do
      case Array.find (\vn -> vn.node.id == nodeId) visualNodes of
        Nothing -> HH.text ""
        Just visualNode -> do
          let node = visualNode.node
          HH.div
            [ HP.class_ (H.ClassName "node-info-panel") ]
            [ HH.h4 [] [ HH.text "Node Information" ]
            , HH.div [] [ HH.text ("File: " <> node.path) ]
            , HH.div [] [ HH.text ("Type: " <> node.type_) ]
            , HH.div [] [ HH.text ("Imports: " <> show (Array.length node.imports)) ]
            , HH.div [] [ HH.text ("Exports: " <> show (Array.length node.exports)) ]
            , HH.div [] [ HH.text ("Complexity: " <> show node.complexity) ]
            , HH.div
                [ HP.class_ (H.ClassName "node-imports") ]
                [ HH.h5 [] [ HH.text "Imports" ]
                , HH.ul [] (Array.map (\imp -> HH.li [] [ HH.text imp ]) node.imports)
                ]
            , HH.div
                [ HP.class_ (H.ClassName "node-exports") ]
                [ HH.h5 [] [ HH.text "Exports" ]
                , HH.ul [] (Array.map (\exp -> HH.li [] [ HH.text exp ]) node.exports)
                ]
            ]

-- | Handle actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    state <- H.get
    case state.graph of
      Nothing -> pure unit
      Just graph -> do
        handleAction (LoadGraph graph)
  
  LoadGraph graph -> do
    -- Calculate circular dependencies
    let circularDeps = findCircularDependencies graph
    
    -- Calculate layout
    let layout = calculateLayout graph
    
    -- Create visual nodes and edges
    let visualNodes = createVisualNodes graph.nodes layout
    let visualEdges = createVisualEdges graph.edges visualNodes
    
    H.modify_ _ 
      { graph = Just graph
      , visualNodes = visualNodes
      , visualEdges = visualEdges
      , circularDependencies = circularDeps
      }
  
  NodeSelected nodeId -> do
    H.modify_ _ { selectedNode = Just nodeId }
    state <- H.get
    case Array.find (\vn -> vn.node.id == nodeId) state.visualNodes of
      Nothing -> pure unit
      Just visualNode -> do
        H.raise (NodeClicked visualNode.node)
        -- Highlight path from selected node
        handleAction (HighlightPath nodeId)
  
  NodeDeselected -> do
    H.modify_ _ { selectedNode = Nothing }
  
  ZoomIn -> do
    H.modify_ \s -> s { zoom = min 3.0 (s.zoom + 0.1) }
  
  ZoomOut -> do
    H.modify_ \s -> s { zoom = max 0.1 (s.zoom - 0.1) }
  
  Pan dx dy -> do
    H.modify_ \s -> s { panX = s.panX + dx, panY = s.panY + dy }
  
  LayoutChanged layoutType -> do
    state <- H.get
    H.modify_ _ { layout = layoutType }
    case state.graph of
      Nothing -> pure unit
      Just graph -> do
        let layout = calculateLayoutForType graph layoutType
        let visualNodes = createVisualNodes graph.nodes layout
        let visualEdges = createVisualEdges graph.edges visualNodes
        H.modify_ _ { visualNodes = visualNodes, visualEdges = visualEdges }
  
  ToggleCircularOnly -> do
    H.modify_ \s -> s { showCircularOnly = not s.showCircularOnly }
    -- Filter nodes and edges to show only circular dependencies
    state <- H.get
    case state.graph of
      Nothing -> pure unit
      Just graph -> do
        if state.showCircularOnly then
          do
            let circularNodeIds = Array.concat state.circularDependencies
            let filteredNodes = Array.filter (\vn -> Array.elem vn.node.id circularNodeIds) state.visualNodes
            let filteredEdges = Array.filter (\ve -> 
                  Array.elem ve.edge.from circularNodeIds && Array.elem ve.edge.to circularNodeIds
                ) state.visualEdges
            H.modify_ _ { visualNodes = filteredNodes, visualEdges = filteredEdges }
        else
          do
            handleAction (LoadGraph graph)
  
  HighlightPath nodeId -> do
    state <- H.get
    case state.graph of
      Nothing -> pure unit
      Just graph -> do
        -- Find transitive dependencies
        let dependencies = findTransitiveDependencies graph nodeId
        let dependents = findTransitiveDependents graph nodeId
        
        -- Highlight nodes in path
        let highlightedNodes = Array.map (\vn ->
              vn { highlighted = Array.elem vn.node.id (dependencies <> dependents <> [nodeId]) }
            ) state.visualNodes
        
        H.modify_ _ { visualNodes = highlightedNodes }

-- | Calculate layout positions for nodes
calculateLayout :: DependencyGraph -> Array { id :: String, x :: Number, y :: Number }
calculateLayout graph = calculateForceDirectedLayout graph

-- | Calculate layout for specific type
calculateLayoutForType :: DependencyGraph -> LayoutType -> Array { id :: String, x :: Number, y :: Number }
calculateLayoutForType graph = case _ of
  ForceDirected -> calculateForceDirectedLayout graph
  Hierarchical -> calculateHierarchicalLayout graph
  Circular -> calculateCircularLayout graph

-- | Force-directed layout (simplified)
calculateForceDirectedLayout :: DependencyGraph -> Array { id :: String, x :: Number, y :: Number }
calculateForceDirectedLayout graph =
  let
    nodeCount = Array.length graph.nodes
    radius = 200.0
    centerX = 400.0
    centerY = 300.0
  in
    Array.mapWithIndex (\index node ->
      let
        angle = 2.0 * Math.pi * Number.fromInt index / Number.fromInt nodeCount
        x = centerX + radius * Math.cos angle
        y = centerY + radius * Math.sin angle
      in
        { id: node.id, x: x, y: y }
    ) graph.nodes

-- | Hierarchical layout
calculateHierarchicalLayout :: DependencyGraph -> Array { id :: String, x :: Number, y :: Number }
calculateHierarchicalLayout graph =
  -- Place root nodes at top, dependencies below
  let
    rootIds = Array.map (\n -> n.id) graph.rootNodes
    levelHeight = 150.0
    startY = 50.0
  in
    Array.mapWithIndex (\index node ->
      let
        isRoot = Array.elem node.id rootIds
        level = if isRoot then 0 else 1
        y = startY + Number.fromInt level * levelHeight
        nodesInLevel = if isRoot then Array.length graph.rootNodes else (Array.length graph.nodes - Array.length graph.rootNodes)
        x = 200.0 + (Number.fromInt index `mod` 10) * 100.0
      in
        { id: node.id, x: x, y: y }
    ) graph.nodes

-- | Circular layout
calculateCircularLayout :: DependencyGraph -> Array { id :: String, x :: Number, y :: Number }
calculateCircularLayout graph =
  let
    nodeCount = Array.length graph.nodes
    radius = 250.0
    centerX = 400.0
    centerY = 300.0
  in
    Array.mapWithIndex (\index node ->
      let
        angle = 2.0 * Math.pi * Number.fromInt index / Number.fromInt nodeCount
        x = centerX + radius * Math.cos angle
        y = centerY + radius * Math.sin angle
      in
        { id: node.id, x: x, y: y }
    ) graph.nodes

-- | Create visual nodes from layout
createVisualNodes :: Array FileNode -> Array { id :: String, x :: Number, y :: Number } -> Array VisualNode
createVisualNodes nodes layout =
  Array.map (\node ->
    case Array.find (\l -> l.id == node.id) layout of
      Nothing -> { node: node, x: 0.0, y: 0.0, selected: false, highlighted: false }
      Just pos -> { node: node, x: pos.x, y: pos.y, selected: false, highlighted: false }
  ) nodes

-- | Create visual edges from nodes
createVisualEdges :: Array DependencyEdge -> Array VisualNode -> Array VisualEdge
createVisualEdges edges visualNodes =
  Array.mapMaybe (\edge ->
    case Array.find (\vn -> vn.node.id == edge.from) visualNodes, Array.find (\vn -> vn.node.id == edge.to) visualNodes of
      Just sourceNode, Just targetNode ->
        Just
          { edge: edge
          , sourceX: sourceNode.x
          , sourceY: sourceNode.y
          , targetX: targetNode.x
          , targetY: targetNode.y
          , highlighted: false
          }
      _, _ -> Nothing
  ) edges

-- | Find transitive dependents (files that depend on this file)
findTransitiveDependents :: DependencyGraph -> String -> Array String
findTransitiveDependents graph nodeId =
  Array.map (\edge -> edge.from) (Array.filter (\edge -> edge.to == nodeId) graph.edges)

-- | Import Math for calculations
import Data.Number as Math
