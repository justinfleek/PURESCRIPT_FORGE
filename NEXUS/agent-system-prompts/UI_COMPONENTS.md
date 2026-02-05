# UI Components for Agent System Prompts

## Status

✅ **PureScript/Halogen Components Created**

Following your **PureScript/Haskell/Lean4 only** language stack.

---

## Created Components

### 1. `AgentOutputViewer.purs` (Main Component)
**Location:** `NEXUS/ui/src/Nexus/AgentOutputViewer.purs`

**Purpose:** Main component that renders structured agent outputs

**Features:**
- Renders all sections conditionally based on output data
- Handles state (details expanded, checklist items)
- Integrates all sub-components

**Usage:**
```purescript
import Nexus.AgentOutputViewer as AgentOutputViewer
import Nexus.AgentOutputViewer.Types as Types

-- Create output data
output :: Types.AgentOutput
output = 
  { status: Types.Success
  , summary: "Fixed type error in src/module/File.ts"
  , whatChanged: Just [...]
  , evidence: Just [...]
  , violations: Nothing
  , nextSteps: Just [...]
  , verification: Just ["npx tsc --noEmit"]
  , details: Just "..."
  , completionChecklist: Just [...]
  }

-- Render component
HH.slot_ (Proxy :: _ "agentOutput") unit AgentOutputViewer.component output
```

---

### 2. `Types.purs` (Type Definitions)
**Location:** `NEXUS/ui/src/Nexus/AgentOutputViewer/Types.purs`

**Purpose:** Type-safe definitions for agent outputs

**Types:**
- `OutputStatus` (Success, Failure, Partial, InProgress)
- `EvidenceType` (Verified, Assumed, NeedsVerification)
- `FileChange` (file, lines, changeType)
- `Violation` (with `ViolationSeverity`)
- `NextStep` (with `StepPriority`)
- `ChecklistItem` (label, checked, inProgress)
- `AgentOutput` (complete output structure)

---

### 3. `Components.purs` (Sub-Components)
**Location:** `NEXUS/ui/src/Nexus/AgentOutputViewer/Components.purs`

**Purpose:** Reusable rendering functions for each section

**Components:**
- `renderStatusHeader` - Status indicator + summary
- `renderEvidenceSection` - Evidence classification (✅ ⚠️ ❓)
- `renderChangesSection` - Files table + changes
- `renderViolationsSection` - Violations summary + details
- `renderNextStepsSection` - Actionable steps with priorities
- `renderVerificationSection` - Commands with copy buttons
- `renderCompletionChecklist` - Interactive checklist

---

### 4. `FFI.js` + `FFI.purs` (Foreign Functions)
**Location:** 
- `NEXUS/ui/src/Nexus/AgentOutputViewer/FFI.js`
- `NEXUS/ui/src/Nexus/AgentOutputViewer/FFI.purs`

**Purpose:** JavaScript interop for clipboard, markdown rendering

**Functions:**
- `copyToClipboard` - Copy text to clipboard
- `renderMarkdown` - Render markdown to HTML (TODO: add markdown library)

---

## Integration with Bridge Server

### Data Flow

```
Agent (Python/Haskell/PureScript)
  ↓
Generates structured output (JSON)
  ↓
Bridge Server (PureScript)
  ↓
WebSocket/HTTP API
  ↓
PureScript/Halogen UI
  ↓
AgentOutputViewer component
  ↓
Renders structured output
```

### Bridge Server Integration

**Add to Bridge Server:**

```purescript
-- In Bridge.NEXUS.Handlers.purs

-- | Handle agent output message
handleAgentOutput :: WebSocketManager -> Json -> Effect Unit
handleAgentOutput wsManager json = do
  -- Parse agent output
  output <- decodeAgentOutput json
  
  -- Broadcast to UI
  broadcastToUI wsManager "agent-output" output
```

---

## Styling

### CSS Classes

All components use semantic CSS classes:

- `.agent-output-viewer` - Main container
- `.status-header` - Status section
- `.status-success`, `.status-failure`, `.status-partial`, `.status-in-progress`
- `.evidence-section` - Evidence list
- `.evidence-verified`, `.evidence-assumed`, `.evidence-needs-verification`
- `.changes-section` - Changes table
- `.files-table` - Files modified table
- `.violations-section` - Violations section
- `.violations-summary` - Summary table
- `.violation-critical`, `.violation-high`, `.violation-medium`, `.violation-low`
- `.next-steps-section` - Next steps list
- `.priority-high`, `.priority-medium`, `.priority-low`
- `.verification-section` - Verification commands
- `.command` - Individual command
- `.copy-button` - Copy button
- `.completion-checklist` - Checklist
- `.checklist-items` - Checklist items
- `.details-section` - Expandable details

### Recommended Styling

```css
/* Status colors */
.status-success { color: #10b981; }
.status-failure { color: #ef4444; }
.status-partial { color: #f59e0b; }
.status-in-progress { color: #3b82f6; }

/* Evidence colors */
.evidence-verified { color: #10b981; }
.evidence-assumed { color: #f59e0b; }
.evidence-needs-verification { color: #3b82f6; }

/* Violation colors */
.violation-critical { border-left: 4px solid #ef4444; }
.violation-high { border-left: 4px solid #f97316; }
.violation-medium { border-left: 4px solid #f59e0b; }
.violation-low { border-left: 4px solid #6b7280; }

/* Priority colors */
.priority-high { color: #ef4444; }
.priority-medium { color: #f59e0b; }
.priority-low { color: #6b7280; }
```

---

## Next Steps

1. **Add Markdown Rendering**
   - Add markdown library dependency
   - Implement `renderMarkdown` in FFI
   - Use in `DetailsSection`

2. **Add Code Diff Viewer**
   - Create `CodeDiffViewer.purs` component
   - Render before/after code with syntax highlighting
   - Use in `ChangesSection` and `ViolationsSection`

3. **Add Clipboard Integration**
   - Complete `copyToClipboard` FFI implementation
   - Wire up copy buttons
   - Add success/error feedback

4. **Add File:Line Links**
   - Make file:line references clickable
   - Open files in editor (via Bridge Server)
   - Highlight specific lines

5. **Add Graph Visualizations**
   - For dependency graphs
   - For network graphs (Network Analyst)
   - Use SVG or canvas

6. **Integrate with Agent Dashboard**
   - Add `AgentOutputViewer` to `AgentDashboard.purs`
   - Show outputs when agent selected
   - Real-time updates via WebSocket

---

## Example Usage

```purescript
-- In AgentDashboard.purs

import Nexus.AgentOutputViewer as AgentOutputViewer
import Nexus.AgentOutputViewer.Types as OutputTypes

-- When agent selected, show output
renderAgentOutput :: forall m. Maybe OutputTypes.AgentOutput -> H.ComponentHTML Action () m
renderAgentOutput Nothing = HH.text "No output available"
renderAgentOutput (Just output) =
  HH.slot_ 
    (Proxy :: _ "agentOutput") 
    unit 
    AgentOutputViewer.component 
    output
```

---

**All components follow PureScript/Halogen patterns and your language stack requirements.**
