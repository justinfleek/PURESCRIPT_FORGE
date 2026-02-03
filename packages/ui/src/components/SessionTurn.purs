-- | Session Turn Component
-- | Migrated from: forge-dev/packages/ui/src/components/session-turn.tsx
-- | Original lines: 772
-- |
-- | Displays a single turn in a conversation session.
-- | Handles user message, assistant response, tool execution, and diffs.
-- |
-- | This module re-exports all SessionTurn submodules for convenience.
-- | The implementation is split across:
-- |   - SessionTurn/Types.purs - Type definitions
-- |   - SessionTurn/Status.purs - Status computation
-- |   - SessionTurn/Component.purs - Main component
-- |
-- | Data Attributes:
-- | - data-component="session-turn": Root container
-- | - data-slot="session-turn-content": Scrollable content area
-- | - data-slot="session-turn-message-container": Message container
-- | - data-slot="session-turn-attachments": Attachment section
-- | - data-slot="session-turn-message-content": Message content
-- | - data-slot="session-turn-sticky": Sticky header area
-- | - data-slot="session-turn-response-trigger": Expand/collapse trigger
-- | - data-slot="session-turn-collapsible-content-inner": Collapsible content
-- | - data-slot="session-turn-summary-section": Response summary
-- | - data-slot="session-turn-accordion": File diff accordion
-- | - data-message: Message ID attribute
-- | - data-expandable: Whether steps are expandable

module UI.Components.SessionTurn
  ( module UI.Components.SessionTurn.Types
  , module UI.Components.SessionTurn.Status
  , module UI.Components.SessionTurn.Component
  ) where

import UI.Components.SessionTurn.Types
import UI.Components.SessionTurn.Status
import UI.Components.SessionTurn.Component
