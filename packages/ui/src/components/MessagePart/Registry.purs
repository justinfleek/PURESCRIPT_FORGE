-- | MessagePart Registry Module
-- | Tool registry and part component mapping.
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/message-part.tsx
-- | This module handles tool registration and lookup.

module UI.Components.MessagePart.Registry
  ( ToolRegistry
  , registerTool
  , getTool
  , getToolInfo
  , registerPartComponent
  , getPartComponent
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Foreign.Object (Object)
import Foreign.Object as Object
import UI.Components.MessagePart.Types (ToolInfo, ToolProps)

-- ═══════════════════════════════════════════════════════════════════════════════
-- TOOL REGISTRY
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tool registry interface
type ToolRegistry =
  { register :: { name :: String, render :: Maybe (ToolProps -> Effect Unit) } -> Effect Unit
  , render :: String -> Effect (Maybe (ToolProps -> Effect Unit))
  }

-- | Register a tool renderer
foreign import registerTool :: { name :: String, render :: Maybe (ToolProps -> Effect Unit) } -> Effect Unit

-- | Get a registered tool renderer
foreign import getTool :: String -> Effect (Maybe (ToolProps -> Effect Unit))

-- | Get tool display info based on tool name and input
getToolInfo :: String -> Object String -> ToolInfo
getToolInfo tool input = case tool of
  "read" ->
    { icon: "glasses"
    , title: "Read"
    , subtitle: Object.lookup "filePath" input >>= extractFilename
    }
  "list" ->
    { icon: "bullet-list"
    , title: "List"
    , subtitle: Object.lookup "path" input >>= extractFilename
    }
  "glob" ->
    { icon: "magnifying-glass-menu"
    , title: "Glob"
    , subtitle: Object.lookup "pattern" input
    }
  "grep" ->
    { icon: "magnifying-glass-menu"
    , title: "Grep"
    , subtitle: Object.lookup "pattern" input
    }
  "webfetch" ->
    { icon: "window-cursor"
    , title: "Web Fetch"
    , subtitle: Object.lookup "url" input
    }
  "task" ->
    { icon: "task"
    , title: case Object.lookup "subagent_type" input of
        Just agentType -> "Agent: " <> agentType
        Nothing -> "Task"
    , subtitle: Object.lookup "description" input
    }
  "bash" ->
    { icon: "console"
    , title: "Shell"
    , subtitle: Object.lookup "description" input
    }
  "edit" ->
    { icon: "code-lines"
    , title: "Edit"
    , subtitle: Object.lookup "filePath" input >>= extractFilename
    }
  "write" ->
    { icon: "code-lines"
    , title: "Write"
    , subtitle: Object.lookup "filePath" input >>= extractFilename
    }
  "apply_patch" ->
    { icon: "code-lines"
    , title: "Patch"
    , subtitle: Nothing
    }
  "todowrite" ->
    { icon: "checklist"
    , title: "Todos"
    , subtitle: Nothing
    }
  "todoread" ->
    { icon: "checklist"
    , title: "Todos"
    , subtitle: Nothing
    }
  "question" ->
    { icon: "bubble-5"
    , title: "Questions"
    , subtitle: Nothing
    }
  _ ->
    { icon: "mcp"
    , title: tool
    , subtitle: Nothing
    }

-- | Extract filename from path
extractFilename :: String -> Maybe String
extractFilename path =
  let parts = splitPath path
  in case parts of
    [] -> Nothing
    xs -> Just (lastElement xs)

-- FFI helpers
foreign import splitPath :: String -> Array String
foreign import lastElement :: Array String -> String

-- ═══════════════════════════════════════════════════════════════════════════════
-- PART COMPONENT REGISTRY
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Part component type
type PartComponent = forall m. (forall a. Effect a -> m a) -> Unit

-- | Register a part component for a type
foreign import registerPartComponent :: String -> (ToolProps -> Effect Unit) -> Effect Unit

-- | Get a registered part component
foreign import getPartComponent :: String -> Effect (Maybe (ToolProps -> Effect Unit))
