# WebGL/WASM Task Visualization Proposal
## Animated Node Graph for Task Display (TensorLake-Inspired)

**Date:** 2026-02-04  
**Status:** Design Proposal

---

## 🎯 **Goal**

Create a stunning, performant WebGL/WASM-based task visualization that:
- Animates task nodes with smooth transitions
- Handles large graphs (1000+ nodes) at 60fps
- Exports to WASM for maximum performance
- Provides interactive exploration (zoom, pan, select)
- Shows real-time task execution flow

---

## 🔍 **Current State**

### **What We Have:**
1. **Basic SVG Visualization** (`NEXUS/ui/src/Nexus/NetworkVisualization.purs`)
   - Static SVG rendering
   - No animation
   - Limited to ~100 nodes before performance degrades
   - No WebGL acceleration

2. **Task Types** (`COMPASS/src/opencode/render/Types/Tasks.purs`)
   - 16 task types defined (T2I, I2I, Chat, etc.)
   - No visualization component

3. **Canvas Charts** (`src/sidepanel-ps/src/Sidepanel/FFI/Recharts.js`)
   - 2D canvas rendering for charts
   - Not suitable for graph visualization

### **What's Missing:**
- ❌ WebGL rendering
- ❌ Node animation
- ❌ WASM export capability
- ❌ Interactive graph exploration
- ❌ Real-time task execution visualization

---

## 🚀 **Proposed Architecture**

### **Technology Stack**

| Layer | Technology | Purpose |
|-------|------------|---------|
| **Rendering** | WebGL 2.0 | GPU-accelerated graphics |
| **Computation** | WASM (Rust/C++) | Physics simulation, layout |
| **Animation** | Custom (requestAnimationFrame) | Smooth 60fps animations |
| **PureScript** | FFI bindings | Type-safe interface |
| **Layout** | Force-directed (WASM) | Graph positioning |

### **Component Structure**

```
src/sidepanel-ps/src/Sidepanel/Components/TaskVisualization/
├── TaskVisualization.purs          # Main Halogen component
├── TaskVisualization.FFI.purs      # PureScript FFI interface
├── TaskVisualization.FFI.js        # JavaScript bridge
├── TaskVisualization.wasm          # WASM module (Rust/C++)
└── TaskVisualization.types.purs    # Type definitions
```

---

## 🎨 **Visual Design (TensorLake-Inspired)**

### **Node Appearance:**
- **Shape:** Rounded rectangles with icons
- **Colors:** Task-type specific (T2I = blue, Chat = green, etc.)
- **Size:** Based on task complexity/execution time
- **Glow:** Pulsing glow for active/executing tasks
- **Border:** Animated border for selected nodes

### **Edge Appearance:**
- **Style:** Curved bezier paths
- **Color:** Gradient from source to target node color
- **Width:** Based on data flow volume
- **Animation:** Particles flowing along edges during execution

### **Animation Features:**
1. **Node Entrance:** Scale + fade-in animation
2. **Node Update:** Smooth position interpolation
3. **Node Selection:** Pulse + scale animation
4. **Edge Flow:** Particle system showing data flow
5. **Layout Transition:** Smooth force-directed layout updates

---

## 🔧 **Technical Implementation**

### **Phase 1: WebGL Foundation**

#### **1.1 WebGL Context Setup**
```purescript
-- TaskVisualization.FFI.purs
foreign import createWebGLContext :: String -> Effect WebGLContext
foreign import resizeCanvas :: WebGLContext -> Number -> Number -> Effect Unit
foreign import clearCanvas :: WebGLContext -> Effect Unit
```

#### **1.2 Shader Programs**
- **Node Shader:** Renders rounded rectangles with glow
- **Edge Shader:** Renders bezier curves with gradients
- **Particle Shader:** Renders animated particles on edges

#### **1.3 Buffer Management**
- **Vertex Buffer:** Node positions, sizes, colors
- **Index Buffer:** Triangle indices for nodes
- **Edge Buffer:** Control points for bezier curves

### **Phase 2: WASM Integration**

#### **2.1 WASM Module (Rust)**
```rust
// task_visualization.rs
#[wasm_bindgen]
pub struct GraphLayout {
    nodes: Vec<Node>,
    edges: Vec<Edge>,
}

#[wasm_bindgen]
impl GraphLayout {
    pub fn new() -> Self { ... }
    pub fn add_node(&mut self, node: Node) { ... }
    pub fn add_edge(&mut self, edge: Edge) { ... }
    pub fn update_layout(&mut self, dt: f32) { ... }
    pub fn get_node_positions(&self) -> Vec<f32> { ... }
}
```

#### **2.2 PureScript FFI**
```purescript
-- TaskVisualization.FFI.purs
foreign import createLayout :: Effect LayoutHandle
foreign import addNode :: LayoutHandle -> NodeData -> Effect Unit
foreign import updateLayout :: LayoutHandle -> Number -> Effect Unit
foreign import getPositions :: LayoutHandle -> Effect (Array Number)
```

### **Phase 3: Animation System**

#### **3.1 Animation Loop**
```purescript
-- TaskVisualization.purs
animate :: forall m. MonadAff m => State -> H.HalogenM State Action Slots Void m Unit
animate state = do
  -- Update WASM layout
  liftEffect $ updateLayout state.layoutHandle 0.016  -- 60fps
  
  -- Get updated positions
  positions <- liftEffect $ getPositions state.layoutHandle
  
  -- Update WebGL buffers
  liftEffect $ updateNodeBuffers state.glContext positions
  
  -- Render frame
  liftEffect $ renderFrame state.glContext
  
  -- Schedule next frame
  void $ H.fork $ do
    delay (Milliseconds 16.0)
    animate state
```

#### **3.2 Interpolation**
- **Position:** Smooth interpolation between layout updates
- **Color:** Color transitions for state changes
- **Scale:** Smooth scaling for selection/hover

### **Phase 4: Interaction**

#### **4.1 Mouse/Touch Handling**
```purescript
-- TaskVisualization.FFI.purs
foreign import pickNode :: WebGLContext -> Number -> Number -> Effect (Maybe String)
foreign import startPan :: WebGLContext -> Number -> Number -> Effect Unit
foreign import updatePan :: WebGLContext -> Number -> Number -> Effect Unit
foreign import zoom :: WebGLContext -> Number -> Number -> Number -> Effect Unit
```

#### **4.2 Selection & Highlighting**
- Click to select node
- Hover to highlight
- Multi-select with Ctrl/Cmd
- Pan with drag
- Zoom with scroll/pinch

---

## 📊 **Performance Targets**

| Metric | Target | Current (SVG) |
|--------|--------|---------------|
| **Max Nodes** | 10,000+ | ~100 |
| **FPS** | 60 | ~30 |
| **Initial Load** | <100ms | ~500ms |
| **Layout Update** | <16ms | ~100ms |
| **Memory** | <100MB | ~50MB |

---

## 🎯 **Features**

### **Core Features:**
1. ✅ **Animated Node Rendering** - Smooth WebGL rendering
2. ✅ **Force-Directed Layout** - WASM-powered physics
3. ✅ **Real-Time Updates** - 60fps animation loop
4. ✅ **Interactive Exploration** - Zoom, pan, select
5. ✅ **Task Type Visualization** - Color-coded by task type

### **Advanced Features:**
6. ✅ **Execution Flow Animation** - Particles on edges
7. ✅ **Node Clustering** - Group related tasks
8. ✅ **Search & Filter** - Highlight matching nodes
9. ✅ **Export to Image** - Screenshot capability
10. ✅ **Export to WASM** - Standalone WASM module

---

## 🔌 **Integration Points**

### **PureScript Component**
```purescript
-- TaskVisualization.purs
type Input =
  { tasks :: Array Task
  , selectedTaskId :: Maybe String
  , executionState :: ExecutionState
  }

type Output =
  = TaskSelected String
  | TaskHovered (Maybe String)
  | ViewportChanged Viewport

component :: forall q m. MonadAff m => H.Component q Input Output m
```

### **Bridge Server Integration**
- WebSocket updates for real-time task execution
- Task state changes trigger node updates
- Execution flow triggers edge animations

---

## 📦 **Dependencies**

### **PureScript:**
```dhall
{ webgl = "https://github.com/purescript-web/purescript-webgl.git"
, effect = "https://github.com/purescript/purescript-effect.git"
}
```

### **JavaScript:**
```json
{
  "dependencies": {
    "@wasm-tool/wasm-pack-plugin": "^1.7.0"
  }
}
```

### **Rust (WASM):**
```toml
[dependencies]
wasm-bindgen = "0.2"
web-sys = "0.3"
```

---

## 🚧 **Implementation Plan**

### **Week 1: Foundation**
- [ ] Set up WebGL context
- [ ] Create basic shader programs
- [ ] Implement node rendering (static)
- [ ] PureScript FFI bindings

### **Week 2: WASM Integration**
- [ ] Create Rust WASM module
- [ ] Implement force-directed layout
- [ ] Wire up WASM ↔ PureScript
- [ ] Test layout performance

### **Week 3: Animation**
- [ ] Implement animation loop
- [ ] Add interpolation system
- [ ] Create particle system for edges
- [ ] Optimize rendering pipeline

### **Week 4: Interaction**
- [ ] Mouse/touch handling
- [ ] Selection system
- [ ] Zoom/pan controls
- [ ] Integration with PureScript component

### **Week 5: Polish**
- [ ] Task type styling
- [ ] Execution state visualization
- [ ] Performance optimization
- [ ] Documentation

---

## 🎨 **Visual Examples**

### **Node States:**
- **Pending:** Gray, static
- **Executing:** Pulsing glow, animated border
- **Completed:** Green checkmark, fade-out
- **Failed:** Red X, shake animation
- **Selected:** Blue outline, scale up

### **Edge States:**
- **Inactive:** Thin gray line
- **Active:** Animated particles flowing
- **Completed:** Solid colored line
- **Failed:** Red dashed line

---

## 🔬 **Research References**

### **TensorLake Approach:**
- Graph-based workflow visualization
- Real-time execution updates
- Interactive node exploration

### **Similar Libraries:**
- **Three.js:** 3D graph visualization
- **Cytoscape.js:** 2D graph with WebGL backend
- **G6 (AntV):** WebGL-accelerated graph visualization
- **vis.js:** Network visualization with physics

### **WASM Examples:**
- **wasm-bindgen:** Rust → WASM → JS
- **emscripten:** C++ → WASM
- **AssemblyScript:** TypeScript → WASM

---

## ✅ **Success Criteria**

1. **Performance:** 60fps with 1000+ nodes
2. **Visual Quality:** Smooth animations, no jank
3. **Interactivity:** Responsive zoom/pan/select
4. **Integration:** Seamless PureScript integration
5. **Export:** WASM module can be used standalone

---

## 🎯 **Next Steps**

1. **Research:** Deep dive into TensorLake's actual visualization
2. **Prototype:** Create minimal WebGL + WASM proof-of-concept
3. **Design:** Finalize visual design and animation specs
4. **Implement:** Build full-featured component
5. **Integrate:** Wire into sidepanel application

---

*"Visualization is not about pretty pictures. It's about understanding complex systems through interactive exploration."*
