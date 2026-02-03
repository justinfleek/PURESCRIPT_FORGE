-- | Solid.js drag-and-drop utilities
-- | Migrated from: forge-dev/packages/app/src/utils/solid-dnd.tsx (56 lines)
module Sidepanel.Utils.SolidDnd
  ( getDraggableId
  , ConstrainDragXAxis
  , ConstrainDragYAxis
  , Transformer
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Foreign (Foreign)

-- | Transformer record for drag constraints
type Transformer =
  { id :: String
  , order :: Int
  , callback :: Transform -> Transform
  }

-- | Transform type (x, y coordinates)
type Transform =
  { x :: Number
  , y :: Number
  }

-- | Drag/drop context type (opaque)
foreign import data DragDropContext :: Type

-- | Get draggable ID from event
-- | Safely extracts the draggable.id string from a drag event
getDraggableId :: Foreign -> Maybe String
getDraggableId event = getDraggableIdImpl event

foreign import getDraggableIdImpl :: Foreign -> Maybe String

-- | Constrain X axis transformer
-- | Sets x coordinate to 0, allowing only vertical dragging
constrainXTransformer :: Transformer
constrainXTransformer =
  { id: "constrain-x-axis"
  , order: 100
  , callback: \transform -> transform { x = 0.0 }
  }

-- | Constrain Y axis transformer
-- | Sets y coordinate to 0, allowing only horizontal dragging
constrainYTransformer :: Transformer
constrainYTransformer =
  { id: "constrain-y-axis"
  , order: 100
  , callback: \transform -> transform { y = 0.0 }
  }

-- | ConstrainDragXAxis component
-- | Adds a transformer that constrains dragging to vertical only
-- | Uses drag/drop context to register/unregister transformer
type ConstrainDragXAxis = Effect Unit

-- | ConstrainDragYAxis component
-- | Adds a transformer that constrains dragging to horizontal only
type ConstrainDragYAxis = Effect Unit

-- | Register constraint on drag start
foreign import addTransformer :: String -> String -> Transformer -> Effect Unit

-- | Unregister constraint on drag end
foreign import removeTransformer :: String -> String -> String -> Effect Unit

-- | Get drag/drop context
foreign import useDragDropContext :: Effect (Maybe DragDropContext)

-- | Register drag start handler
foreign import onDragStart :: (Foreign -> Effect Unit) -> Effect Unit

-- | Register drag end handler
foreign import onDragEnd :: (Foreign -> Effect Unit) -> Effect Unit

-- | Implementation of ConstrainDragXAxis
constrainDragXAxisImpl :: Effect Unit
constrainDragXAxisImpl = do
  maybeContext <- useDragDropContext
  case maybeContext of
    Nothing -> pure unit
    Just _ -> do
      onDragStart \event -> do
        case getDraggableId event of
          Nothing -> pure unit
          Just id -> addTransformer "draggables" id constrainXTransformer
      
      onDragEnd \event -> do
        case getDraggableId event of
          Nothing -> pure unit
          Just id -> removeTransformer "draggables" id constrainXTransformer.id

-- | Implementation of ConstrainDragYAxis
constrainDragYAxisImpl :: Effect Unit
constrainDragYAxisImpl = do
  maybeContext <- useDragDropContext
  case maybeContext of
    Nothing -> pure unit
    Just _ -> do
      onDragStart \event -> do
        case getDraggableId event of
          Nothing -> pure unit
          Just id -> addTransformer "draggables" id constrainYTransformer
      
      onDragEnd \event -> do
        case getDraggableId event of
          Nothing -> pure unit
          Just id -> removeTransformer "draggables" id constrainYTransformer.id
