# NEXUS Panel Integration Audit
## Current Status & Missing Features

**Date:** 2026-02-04  
**Status:** ❌ **NOT INTEGRATED** - Critical gaps identified

---

## 🔍 **Current State**

### ✅ **What Exists (Backend/Infrastructure):**

1. **NEXUS UI Components** (`NEXUS/ui/src/Nexus/`)
   - ✅ `AgentDashboard.purs` - Agent list/dashboard (basic, TODO comments)
   - ✅ `AgentFeed.purs` - Agent feed/social (basic, TODO comments)
   - ✅ `AgentOutputViewer.purs` - Structured output rendering (complete)
   - ✅ `NetworkVisualization.purs` - Network graph visualization (SVG-based)

2. **Agent Launcher** (`NEXUS/agent-orchestrator-ps/`)
   - ✅ `Launcher.purs` - Agent launch logic
   - ✅ `Types.purs` - Agent types and configs
   - ✅ `Manager.purs` - Agent management

3. **Bridge Server Handlers** (`NEXUS/bridge-server-ps/src/Bridge/NEXUS/`)
   - ✅ `Handlers.purs` - `nexusAgentLaunch`, `nexusAgentStatus`
   - ✅ Edge-aware routing
   - ✅ JSON-RPC 2.0 protocol

4. **System Prompts** (`NEXUS/agent-system-prompts/`)
   - ✅ 9 agent system prompts (deterministic-coder, exploratory-architect, etc.)
   - ✅ Output format protocol
   - ✅ UI components documentation

5. **Model Selection Components** (`src/sidepanel-ps/src/Sidepanel/Components/`)
   - ✅ `ModelPicker.purs` - Full model selection modal
   - ✅ `ModelSelector.purs` - Compact dropdown
   - ✅ `ModelComparison.purs` - Side-by-side comparison

6. **Provider Management** (`packages/app/src/hooks/`)
   - ✅ `UseProviders.purs` - Provider hook (not integrated)

---

## ❌ **What's Missing (Integration & UI):**

### **1. NEXUS Panel NOT Integrated** ❌

**Status:** NEXUS components exist but are **NOT** integrated into sidepanel App

**Missing:**
- ❌ No import of NEXUS components in `App.purs`
- ❌ No route for NEXUS panel
- ❌ No slot for AgentDashboard/AgentFeed
- ❌ No navigation to NEXUS panel

**Files Checked:**
- `src/sidepanel-ps/src/Sidepanel/App.purs` - No NEXUS imports
- `src/sidepanel-ps/src/Sidepanel/Router.purs` - No NEXUS route

---

### **2. Agent Launcher UI Missing** ❌

**Status:** Backend exists, but **NO UI** for launching agents

**Missing:**
- ❌ No "Launch Agent" button/interface
- ❌ No agent type selection UI
- ❌ No agent configuration form
- ❌ No agent status display
- ❌ No agent list/management UI

**What Users Need:**
```
┌─────────────────────────────────────┐
│  LAUNCH AGENT                       │
├─────────────────────────────────────┤
│  Agent Type: [Dropdown ▼]           │
│    - Deterministic Coder            │
│    - Exploratory Architect          │
│    - Expert Researcher              │
│    - Web Search Agent               │
│    - ...                            │
│                                     │
│  Provider: [Dropdown ▼]             │
│    - Venice AI                      │
│    - OpenAI                        │
│    - Anthropic                      │
│                                     │
│  Model: [Dropdown ▼]                 │
│    - llama-3.3-70b                 │
│    - deepseek-r1-70b               │
│    - ...                            │
│                                     │
│  System Prompt: [Dropdown ▼]        │
│    - Use default                   │
│    - Custom prompt                 │
│    - Load from file                │
│                                     │
│  Hosting: [Radio]                   │
│    ○ Local (sandbox)                │
│    ○ Edge (closest region)          │
│                                     │
│  [Launch Agent] [Cancel]            │
└─────────────────────────────────────┘
```

---

### **3. Provider Selection NOT Integrated** ❌

**Status:** `UseProviders` hook exists but **NOT** used in UI

**Missing:**
- ❌ No provider selection dropdown
- ❌ No provider connection UI
- ❌ No provider settings/config
- ❌ No API key management

**What Exists:**
- ✅ `UseProviders.purs` hook (not imported anywhere)
- ✅ Provider types defined

**What's Needed:**
- Provider selection component
- Provider connection flow
- API key input/management
- Provider status display

---

### **4. Model Selection NOT Fully Wired** ⚠️

**Status:** Components exist but **NOT** integrated into main flow

**Missing:**
- ⚠️ ModelPicker/ModelSelector not in App.purs
- ⚠️ No easy access from session creation
- ⚠️ No model selection in agent launch flow

**What Exists:**
- ✅ `ModelPicker.purs` - Full modal
- ✅ `ModelSelector.purs` - Compact dropdown
- ✅ `ModelComparison.purs` - Comparison view

**What's Needed:**
- Wire ModelSelector into session creation
- Wire ModelPicker into agent launch
- Add model selection to settings

---

### **5. System Prompt Configuration Missing** ❌

**Status:** System prompts exist but **NO UI** for configuration

**Missing:**
- ❌ No system prompt editor
- ❌ No prompt template selector
- ❌ No prompt variable configuration
- ❌ No prompt preview
- ❌ No prompt management (create/edit/delete)

**What Exists:**
- ✅ 9 system prompt files in `NEXUS/agent-system-prompts/`
- ✅ Spec in `29-SYSTEM-PROMPTS.md`
- ✅ Prompt templates defined

**What's Needed:**
```purescript
-- System Prompt Configuration Component
type SystemPromptConfig =
  { promptId :: String
  , template :: String
  , variables :: Array PromptVariable
  , preview :: String
  }

-- UI Components:
- SystemPromptSelector (dropdown)
- SystemPromptEditor (full editor)
- SystemPromptPreview (rendered preview)
- SystemPromptManager (create/edit/delete)
```

---

### **6. Hosting/Region Selection Missing** ❌

**Status:** Edge routing exists but **NO UI** for selection

**Missing:**
- ❌ No hosting option selector (Local vs Edge)
- ❌ No region selector
- ❌ No latency display
- ❌ No hosting status

**What Exists:**
- ✅ Edge routing logic in `Bridge.NEXUS.EdgeRouting`
- ✅ Region detection

**What's Needed:**
- Hosting selector component
- Region selector with latency
- Hosting status display

---

## 🎯 **What Users Need: Complete Agent Launch Flow**

### **Ideal User Experience:**

```
1. User clicks "Launch Agent" (or Ctrl+Shift+A)
   ↓
2. Agent Launcher Modal opens
   ├─ Agent Type Selection (with descriptions)
   ├─ Provider Selection (with connection status)
   ├─ Model Selection (with recommendations)
   ├─ System Prompt Selection/Editor
   ├─ Hosting Selection (Local/Edge)
   └─ Advanced Options (sandbox config, etc.)
   ↓
3. User clicks "Launch"
   ↓
4. Agent launches, status shown in real-time
   ↓
5. Agent appears in Agent Dashboard
   ↓
6. User can view agent output, status, logs
```

---

## 🔧 **Implementation Plan**

### **Phase 1: NEXUS Panel Integration**

#### **1.1 Add NEXUS Route**
```purescript
-- Router.purs
data Route
  = Dashboard
  | Session (Maybe String)
  | Proof
  | Timeline
  | Settings
  | Nexus  -- NEW
  | ...
```

#### **1.2 Add NEXUS Panel to App**
```purescript
-- App.purs
import Nexus.AgentDashboard as AgentDashboard
import Nexus.AgentFeed as AgentFeed

-- Add slot
type Slots = ( ... , nexusDashboard :: H.Slot AgentDashboard.Query Void Unit )

-- Add route handler
renderCurrentPanel state = case state.currentRoute of
  Nexus -> HH.slot _nexusDashboard unit AgentDashboard.component unit (const HandleNexusOutput)
  ...
```

#### **1.3 Add Navigation**
```purescript
-- Sidebar.purs
-- Add "NEXUS" navigation item
```

---

### **Phase 2: Agent Launcher UI**

#### **2.1 Create AgentLauncher Component**
```purescript
-- src/sidepanel-ps/src/Sidepanel/Components/Nexus/AgentLauncher.purs

type Input = { visible :: Boolean, wsClient :: Maybe WS.WSClient }

type State =
  { agentType :: Maybe AgentType
  , provider :: Maybe String
  , model :: Maybe String
  , systemPrompt :: Maybe String
  , hosting :: HostingOption
  , config :: AgentConfig
  }

data HostingOption = LocalHosting | EdgeHosting (Maybe String)

component :: forall q m. MonadAff m => H.Component q Input Output m
```

#### **2.2 Wire to Bridge API**
```purescript
-- AgentLauncher.purs handleAction
LaunchAgent -> do
  state <- H.get
  case state.wsClient of
    Just client -> do
      result <- liftEffect $ Bridge.nexusAgentLaunch client
        { agentType: fromMaybe "web_search" state.agentType
        , config: encodeAgentConfig state.config
        }
      case result of
        Right response -> H.raise (AgentLaunched response.agentId)
        Left err -> H.modify_ _ { error = Just err.message }
    Nothing -> H.modify_ _ { error = Just "Not connected" }
```

---

### **Phase 3: Provider Selection**

#### **3.1 Create ProviderSelector Component**
```purescript
-- src/sidepanel-ps/src/Sidepanel/Components/Provider/ProviderSelector.purs

type Provider =
  { id :: String
  , name :: String
  , connected :: Boolean
  , apiKeyRequired :: Boolean
  }

component :: forall q m. MonadAff m => H.Component q Input Output m
```

#### **3.2 Add Provider Connection Flow**
```purescript
-- ProviderSelector.purs
ConnectProvider providerId -> do
  -- Show API key input modal
  -- Save to settings
  -- Test connection
  -- Update connection status
```

---

### **Phase 4: System Prompt Configuration**

#### **4.1 Create SystemPromptEditor Component**
```purescript
-- src/sidepanel-ps/src/Sidepanel/Components/SystemPrompt/SystemPromptEditor.purs

type SystemPrompt =
  { id :: String
  , name :: String
  , template :: String
  , variables :: Array PromptVariable
  }

component :: forall q m. MonadAff m => H.Component q Input Output m
```

#### **4.2 Load System Prompts**
```purescript
-- Load from NEXUS/agent-system-prompts/
-- Parse markdown files
-- Extract templates and variables
-- Provide editor with syntax highlighting
```

---

### **Phase 5: Hosting Selection**

#### **5.1 Create HostingSelector Component**
```purescript
-- src/sidepanel-ps/src/Sidepanel/Components/Hosting/HostingSelector.purs

type HostingOption =
  { type_ :: HostingType  -- Local | Edge
  , region :: Maybe String
  , latency :: Maybe Number  -- ms
  }

component :: forall q m. MonadAff m => H.Component q Input Output m
```

---

## 📋 **Integration Checklist**

### **NEXUS Panel:**
- [ ] Add NEXUS route to Router
- [ ] Import AgentDashboard into App.purs
- [ ] Add NEXUS slot to App.purs
- [ ] Add NEXUS navigation to Sidebar
- [ ] Wire AgentDashboard to Bridge API
- [ ] Wire AgentFeed to Bridge API

### **Agent Launcher:**
- [ ] Create AgentLauncher component
- [ ] Add agent type selection
- [ ] Add provider selection (integrate ProviderSelector)
- [ ] Add model selection (integrate ModelSelector)
- [ ] Add system prompt selection/editor
- [ ] Add hosting selection
- [ ] Wire to Bridge.nexusAgentLaunch
- [ ] Add launch button to QuickActions
- [ ] Add keyboard shortcut (Ctrl+Shift+A)

### **Provider Selection:**
- [ ] Create ProviderSelector component
- [ ] Load providers from UseProviders hook
- [ ] Add provider connection flow
- [ ] Add API key input/management
- [ ] Add provider status display
- [ ] Integrate into AgentLauncher
- [ ] Integrate into Settings

### **Model Selection:**
- [ ] Wire ModelSelector into session creation
- [ ] Wire ModelPicker into agent launch
- [ ] Add model selection to Settings
- [ ] Add model recommendations

### **System Prompt:**
- [ ] Create SystemPromptEditor component
- [ ] Load system prompts from files
- [ ] Add prompt template selector
- [ ] Add prompt variable editor
- [ ] Add prompt preview
- [ ] Add prompt management (CRUD)
- [ ] Integrate into AgentLauncher

### **Hosting Selection:**
- [ ] Create HostingSelector component
- [ ] Add Local/Edge radio buttons
- [ ] Add region selector (if Edge)
- [ ] Display latency for regions
- [ ] Integrate into AgentLauncher

---

## 🚨 **Critical Gaps Summary**

| Feature | Backend | UI Component | Integration | Status |
|---------|---------|--------------|-------------|--------|
| **NEXUS Panel** | ✅ Exists | ✅ Exists | ❌ Missing | ❌ **NOT INTEGRATED** |
| **Agent Launcher** | ✅ Exists | ❌ Missing | ❌ Missing | ❌ **NO UI** |
| **Provider Selection** | ✅ Hook exists | ❌ Missing | ❌ Missing | ❌ **NO UI** |
| **Model Selection** | ✅ Exists | ✅ Exists | ⚠️ Partial | ⚠️ **NOT WIRED** |
| **System Prompt** | ✅ Files exist | ❌ Missing | ❌ Missing | ❌ **NO UI** |
| **Hosting Selection** | ✅ Logic exists | ❌ Missing | ❌ Missing | ❌ **NO UI** |

---

## ✅ **What Needs to Be Built**

### **Priority 1: Critical (This Week)**
1. **Agent Launcher Component** - Complete UI for launching agents
2. **NEXUS Panel Integration** - Wire AgentDashboard into App
3. **Provider Selector** - Provider selection and connection
4. **System Prompt Selector** - Load and select system prompts

### **Priority 2: High (Next Week)**
5. **System Prompt Editor** - Edit and create custom prompts
6. **Hosting Selector** - Local vs Edge selection
7. **Model Selection Integration** - Wire into agent launch flow
8. **Agent Status Display** - Real-time agent status

### **Priority 3: Nice to Have**
9. **Agent Management** - List, stop, restart agents
10. **Agent Output Viewer Integration** - Show outputs in dashboard
11. **Agent Feed Integration** - Social feed for agents

---

## 🎯 **Recommended Implementation Order**

1. **Step 1:** Create AgentLauncher component (most critical)
2. **Step 2:** Integrate NEXUS panel into App (enables dashboard)
3. **Step 3:** Create ProviderSelector component
4. **Step 4:** Create SystemPromptSelector component
5. **Step 5:** Wire everything together in AgentLauncher
6. **Step 6:** Add HostingSelector
7. **Step 7:** Integrate ModelSelector into flow

---

*"Users need a one-click way to launch agents with full configuration. Currently, they have to manually call APIs or use command-line tools. This is unacceptable for a professional AI coding assistant."*
