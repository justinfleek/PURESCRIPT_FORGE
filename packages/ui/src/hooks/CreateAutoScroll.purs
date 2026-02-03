-- | Auto Scroll Hook - Automatic Scroll Management
-- |
-- | Provides automatic scrolling behavior for streaming content:
-- | - Keeps content pinned to bottom while working
-- | - Detects user scroll interaction to pause auto-scroll
-- | - Handles resize events to maintain scroll position
-- | - Supports overflow anchor control
-- |
-- | Source: _OTHER/opencode-original/packages/ui/src/hooks/create-auto-scroll.tsx
module Forge.UI.Hooks.CreateAutoScroll
  ( AutoScrollOptions
  , AutoScrollState
  , createAutoScroll
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Web.HTML.HTMLElement (HTMLElement)

-- | Auto scroll options
type AutoScrollOptions =
  { working :: Effect Boolean
  , onUserInteracted :: Maybe (Effect Unit)
  , overflowAnchor :: Maybe String  -- "none" | "auto" | "dynamic"
  , bottomThreshold :: Maybe Int
  }

-- | Auto scroll state and controls
type AutoScrollState =
  { scrollRef :: Maybe HTMLElement -> Effect Unit
  , contentRef :: Maybe HTMLElement -> Effect Unit
  , handleScroll :: Effect Unit
  , handleInteraction :: Effect Unit
  , pause :: Effect Unit
  , resume :: Effect Unit
  , scrollToBottom :: Effect Unit
  , forceScrollToBottom :: Effect Unit
  , userScrolled :: Effect Boolean
  }

-- | Get distance from bottom of scrollable element
foreign import distanceFromBottom :: HTMLElement -> Effect Int

-- | Check if element can scroll
foreign import canScroll :: HTMLElement -> Effect Boolean

-- | Scroll element to bottom
foreign import scrollToBottomNow :: HTMLElement -> String -> Effect Unit

-- | Add wheel event listener
foreign import addWheelListener :: HTMLElement -> (Int -> Effect Unit) -> Effect (Effect Unit)

-- | Update overflow anchor style
foreign import setOverflowAnchor :: HTMLElement -> String -> Effect Unit

-- | Create auto scroll behavior
createAutoScroll :: AutoScrollOptions -> Effect AutoScrollState
createAutoScroll options = do
  scrollRef <- Ref.new (Nothing :: Maybe HTMLElement)
  contentRef <- Ref.new (Nothing :: Maybe HTMLElement)
  userScrolledRef <- Ref.new false
  settlingRef <- Ref.new false
  cleanupRef <- Ref.new (Nothing :: Maybe (Effect Unit))
  
  let
    threshold = case options.bottomThreshold of
      Just t -> t
      Nothing -> 10
    
    active = do
      working <- options.working
      settling <- Ref.read settlingRef
      pure (working || settling)
    
    scrollToBottom' :: Boolean -> Effect Unit
    scrollToBottom' force = do
      mScroll <- Ref.read scrollRef
      case mScroll of
        Nothing -> pure unit
        Just scroll -> do
          isActive <- active
          when (force || isActive) do
            userScrolled <- Ref.read userScrolledRef
            when (force || not userScrolled) do
              dist <- distanceFromBottom scroll
              when (dist >= 2) do
                scrollToBottomNow scroll "auto"
    
    stop = do
      mScroll <- Ref.read scrollRef
      case mScroll of
        Nothing -> pure unit
        Just scroll -> do
          cs <- canScroll scroll
          if not cs
            then do
              userScrolled <- Ref.read userScrolledRef
              when userScrolled (Ref.write false userScrolledRef)
            else do
              userScrolled <- Ref.read userScrolledRef
              when (not userScrolled) do
                Ref.write true userScrolledRef
                case options.onUserInteracted of
                  Just callback -> callback
                  Nothing -> pure unit
    
    handleScroll = do
      mScroll <- Ref.read scrollRef
      case mScroll of
        Nothing -> pure unit
        Just scroll -> do
          cs <- canScroll scroll
          if not cs
            then do
              userScrolled <- Ref.read userScrolledRef
              when userScrolled (Ref.write false userScrolledRef)
            else do
              dist <- distanceFromBottom scroll
              if dist < threshold
                then do
                  userScrolled <- Ref.read userScrolledRef
                  when userScrolled (Ref.write false userScrolledRef)
                else stop
    
    handleInteraction = do
      isActive <- active
      when isActive stop
    
    setScrollRef mEl = do
      -- Cleanup previous
      mCleanup <- Ref.read cleanupRef
      case mCleanup of
        Just cleanup -> cleanup
        Nothing -> pure unit
      Ref.write Nothing cleanupRef
      
      Ref.write mEl scrollRef
      
      case mEl of
        Nothing -> pure unit
        Just el -> do
          -- Set overflow anchor
          let anchor = case options.overflowAnchor of
                Just a -> a
                Nothing -> "dynamic"
          setOverflowAnchor el anchor
          
          -- Add wheel listener
          cleanup <- addWheelListener el \deltaY ->
            when (deltaY < 0) stop
          Ref.write (Just cleanup) cleanupRef
    
    setContentRef mEl = Ref.write mEl contentRef

  pure
    { scrollRef: setScrollRef
    , contentRef: setContentRef
    , handleScroll
    , handleInteraction
    , pause: stop
    , resume: do
        Ref.write false userScrolledRef
        scrollToBottom' true
    , scrollToBottom: scrollToBottom' false
    , forceScrollToBottom: scrollToBottom' true
    , userScrolled: Ref.read userScrolledRef
    }
