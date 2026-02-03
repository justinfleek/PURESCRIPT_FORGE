-- | DOM selection utilities for code editor integration
-- | Migrated from: forge-dev/packages/app/src/utils/dom.ts (52 lines)
module Sidepanel.Utils.Dom
  ( getCharacterOffsetInLine
  , getNodeOffsetInLine
  , getSelectionInContainer
  , NodeOffset
  , SelectionRange
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)

-- | Result of finding a node offset in a line
type NodeOffset =
  { node :: Node
  , offset :: Int
  }

-- | Selection range within a container
-- | sl = start line (1-based)
-- | sch = start character
-- | el = end line (1-based)  
-- | ech = end character
type SelectionRange =
  { sl :: Int
  , sch :: Int
  , el :: Int
  , ech :: Int
  }

-- | Foreign DOM types
foreign import data Node :: Type
foreign import data Element :: Type
foreign import data HTMLElement :: Type

-- | Get the character offset within a line element
-- | Uses Range API to measure text content
-- | @param lineElement - The line container element
-- | @param targetNode - The node containing the cursor
-- | @param offset - The offset within the target node
-- | @return Character offset from start of line
getCharacterOffsetInLine :: Element -> Node -> Int -> Effect Int
getCharacterOffsetInLine lineElement targetNode offset = do
  -- Create range, select line contents, set end to target
  -- Return range.toString().length
  getCharacterOffsetInLineImpl lineElement targetNode offset

foreign import getCharacterOffsetInLineImpl :: Element -> Node -> Int -> Effect Int

-- | Get the node and offset for a character index within a line
-- | Walks the DOM tree counting characters to find position
-- | @param lineElement - The line container element
-- | @param charIndex - The target character index
-- | @return Node and offset, or Nothing if not found
getNodeOffsetInLine :: Element -> Int -> Effect (Maybe NodeOffset)
getNodeOffsetInLine lineElement charIndex = do
  -- Use TreeWalker to iterate text nodes
  -- Track remaining characters until we find the target position
  getNodeOffsetInLineImpl lineElement charIndex

foreign import getNodeOffsetInLineImpl :: Element -> Int -> Effect (Maybe NodeOffset)

-- | Get the current selection within a container
-- | Maps window selection to line numbers and character offsets
-- | @param container - The container element (usually code block)
-- | @return Selection range with 1-based line numbers, or Nothing
getSelectionInContainer :: HTMLElement -> Effect (Maybe SelectionRange)
getSelectionInContainer container = do
  -- Get window selection
  -- Find .line elements containing start/end
  -- Calculate line indices (1-based) and character offsets
  getSelectionInContainerImpl container

foreign import getSelectionInContainerImpl :: HTMLElement -> Effect (Maybe SelectionRange)
