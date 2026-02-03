-- | Message Part Component
-- | Migrated from: forge-dev/packages/ui/src/components/message-part.tsx
-- | Original lines: 1577
-- |
-- | Comprehensive message rendering system with tool registry.
-- | Handles user messages, assistant messages, and tool outputs.
-- |
-- | This module re-exports all MessagePart submodules for convenience.
-- | The implementation is split across:
-- |   - MessagePart/Types.purs - Type definitions
-- |   - MessagePart/Registry.purs - Tool registry
-- |   - MessagePart/Component.purs - Main components
-- |
-- | Data Attributes:
-- | - data-component="user-message": User message container
-- | - data-component="text-part": Text content part
-- | - data-component="reasoning-part": Reasoning content
-- | - data-component="tool-part-wrapper": Tool output wrapper
-- | - data-component="permission-prompt": Permission request UI
-- | - data-component="question-prompt": Question request UI
-- | - data-component="diagnostics": Diagnostics display
-- | - data-component="tool-output": Tool output content
-- | - data-component="tool-error": Error display
-- | - data-component="todos": Todo list display
-- | - data-slot="*": Various slots for content organization

module UI.Components.MessagePart
  ( module UI.Components.MessagePart.Types
  , module UI.Components.MessagePart.Registry
  , module UI.Components.MessagePart.Component
  ) where

import UI.Components.MessagePart.Types
import UI.Components.MessagePart.Registry
import UI.Components.MessagePart.Component
