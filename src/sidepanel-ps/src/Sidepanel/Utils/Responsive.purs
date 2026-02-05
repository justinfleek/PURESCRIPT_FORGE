-- | Responsive Layout Utilities - Screen Size Detection and Layout Modes
-- |
-- | **What:** Provides utilities for detecting screen size, layout mode, and responsive
-- |         breakpoints. Enables components to adapt their rendering based on viewport size.
-- | **Why:** Ensures the sidepanel works well across different screen sizes (sidebar, floating,
-- |         tablet, mobile).
-- | **How:** Uses FFI to detect window dimensions and provides PureScript functions for
-- |         breakpoint detection and layout mode determination.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.FFI.Window`: Window dimension detection
-- |
-- | **Mathematical Foundation:**
-- | - **Breakpoint Invariant:** Breakpoints are mutually exclusive and cover all viewport sizes.
-- | - **Layout Mode Invariant:** Layout mode is determined solely by viewport width.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Utils.Responsive as Responsive
-- |
-- | -- Detect layout mode
-- | mode <- liftEffect Responsive.getLayoutMode
-- | case mode of
-- |   Responsive.SidebarMode -> renderSidebarLayout
-- |   Responsive.MobileMode -> renderMobileLayout
-- | ```
-- |
-- | Based on spec 84-RESPONSIVE-LAYOUT.md
module Sidepanel.Utils.Responsive where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe(..))

-- | Layout mode
data LayoutMode
  = SidebarMode  -- 300-400px: Docked sidebar beside editor
  | FloatingMode  -- 400-800px: Standalone floating window
  | TabletMode  -- 768-1024px: Tablet with touch
  | MobileMode  -- 320-767px: Mobile single-column

derive instance eqLayoutMode :: Eq LayoutMode

-- | Breakpoints (in pixels)
type Breakpoints =
  { mobile :: Number  -- 320px
  , mobileLarge :: Number  -- 480px
  , tablet :: Number  -- 768px
  , desktop :: Number  -- 1024px
  , wide :: Number  -- 1440px
  }

-- | Default breakpoints
defaultBreakpoints :: Breakpoints
defaultBreakpoints =
  { mobile: 320.0
  , mobileLarge: 480.0
  , tablet: 768.0
  , desktop: 1024.0
  , wide: 1440.0
  }

import Sidepanel.FFI.Window as Window

-- | Get current viewport width
getViewportWidth :: Effect Number
getViewportWidth = Window.getViewportWidth

-- | Get current viewport height
getViewportHeight :: Effect Number
getViewportHeight = Window.getViewportHeight

-- | Get layout mode based on viewport width
getLayoutMode :: Effect LayoutMode
getLayoutMode = do
  width <- getViewportWidth
  pure $ determineLayoutMode width

-- | Determine layout mode from width
determineLayoutMode :: Number -> LayoutMode
determineLayoutMode width
  | width < 480.0 = MobileMode
  | width < 768.0 = SidebarMode
  | width < 1024.0 = TabletMode
  | otherwise = FloatingMode

-- | Check if viewport is mobile
isMobile :: Effect Boolean
isMobile = do
  mode <- getLayoutMode
  pure $ mode == MobileMode

-- | Check if viewport is tablet
isTablet :: Effect Boolean
isTablet = do
  mode <- getLayoutMode
  pure $ mode == TabletMode

-- | Check if viewport is sidebar mode
isSidebar :: Effect Boolean
isSidebar = do
  mode <- getLayoutMode
  pure $ mode == SidebarMode

-- | Check if viewport is floating mode
isFloating :: Effect Boolean
isFloating = do
  mode <- getLayoutMode
  pure $ mode == FloatingMode

-- | Get CSS class name for layout mode
layoutModeClass :: LayoutMode -> String
layoutModeClass = case _ of
  SidebarMode -> "layout-sidebar"
  FloatingMode -> "layout-floating"
  TabletMode -> "layout-tablet"
  MobileMode -> "layout-mobile"
