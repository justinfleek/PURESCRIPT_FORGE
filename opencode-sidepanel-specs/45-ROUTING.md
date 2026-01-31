# 45-ROUTING: SPA Navigation System

## Overview

The routing system provides client-side navigation between views (Dashboard, Sessions, Proofs, Timeline, Settings, etc.) with keyboard shortcuts, deep linking, and history management.

---

## Route Structure

```
/                      → Dashboard (redirect)
/dashboard             → Dashboard view
/session               → Current session
/session/:id           → Specific session
/session/:id/message/:msgId → Jump to message
/files                 → File context view
/diff                  → Diff viewer
/proofs                → Proofs panel
/proofs/:file          → Specific proof file
/timeline              → Timeline view
/timeline/:snapshotId  → Jump to snapshot
/recordings            → Recording library
/recordings/:id        → Playback specific recording
/search                → Search view
/search?q=:query       → Search with query
/performance           → Performance profiler
/settings              → Settings panel
/settings/:section     → Specific settings section
```

---

## Route Data Types

```purescript
module Sidepanel.Routing where

import Prelude
import Data.Maybe (Maybe)
import Data.Either (Either)

-- All possible routes
data Route
  = Dashboard
  | Session (Maybe SessionRoute)
  | Files
  | Diff
  | Proofs (Maybe ProofRoute)
  | Timeline (Maybe String)  -- snapshot ID
  | Recordings (Maybe String)  -- recording ID
  | Search (Maybe String)  -- query
  | Performance
  | Settings (Maybe SettingsSection)
  | NotFound String

data SessionRoute
  = CurrentSession
  | SpecificSession String
  | SessionMessage String String  -- session ID, message ID

data ProofRoute
  = AllProofs
  | ProofFile String

data SettingsSection
  = GeneralSettings
  | AppearanceSettings
  | KeyboardSettings
  | AdvancedSettings

derive instance eqRoute :: Eq Route
derive instance genericRoute :: Generic Route _

-- Route matching
parseRoute :: String -> Route
parseRoute path = case split (Pattern "/") (drop 1 path) of
  [""] -> Dashboard
  ["dashboard"] -> Dashboard
  ["session"] -> Session (Just CurrentSession)
  ["session", id] -> Session (Just (SpecificSession id))
  ["session", id, "message", msgId] -> Session (Just (SessionMessage id msgId))
  ["files"] -> Files
  ["diff"] -> Diff
  ["proofs"] -> Proofs (Just AllProofs)
  ["proofs", file] -> Proofs (Just (ProofFile file))
  ["timeline"] -> Timeline Nothing
  ["timeline", snapId] -> Timeline (Just snapId)
  ["recordings"] -> Recordings Nothing
  ["recordings", id] -> Recordings (Just id)
  ["search"] -> Search Nothing
  ["performance"] -> Performance
  ["settings"] -> Settings Nothing
  ["settings", section] -> Settings (parseSettingsSection section)
  other -> NotFound (joinWith "/" other)

parseSettingsSection :: String -> Maybe SettingsSection
parseSettingsSection = case _ of
  "general" -> Just GeneralSettings
  "appearance" -> Just AppearanceSettings
  "keyboard" -> Just KeyboardSettings
  "advanced" -> Just AdvancedSettings
  _ -> Nothing

-- Route printing
printRoute :: Route -> String
printRoute = case _ of
  Dashboard -> "/dashboard"
  Session Nothing -> "/session"
  Session (Just CurrentSession) -> "/session"
  Session (Just (SpecificSession id)) -> "/session/" <> id
  Session (Just (SessionMessage id msgId)) -> "/session/" <> id <> "/message/" <> msgId
  Files -> "/files"
  Diff -> "/diff"
  Proofs Nothing -> "/proofs"
  Proofs (Just AllProofs) -> "/proofs"
  Proofs (Just (ProofFile file)) -> "/proofs/" <> file
  Timeline Nothing -> "/timeline"
  Timeline (Just snapId) -> "/timeline/" <> snapId
  Recordings Nothing -> "/recordings"
  Recordings (Just id) -> "/recordings/" <> id
  Search Nothing -> "/search"
  Search (Just q) -> "/search?q=" <> encodeURIComponent q
  Performance -> "/performance"
  Settings Nothing -> "/settings"
  Settings (Just section) -> "/settings/" <> printSettingsSection section
  NotFound _ -> "/dashboard"

printSettingsSection :: SettingsSection -> String
printSettingsSection = case _ of
  GeneralSettings -> "general"
  AppearanceSettings -> "appearance"
  KeyboardSettings -> "keyboard"
  AdvancedSettings -> "advanced"
```

---

## Router Component

```purescript
module Sidepanel.Router where

import Prelude
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Data.Maybe (Maybe(..))
import Routing.Hash (matchesWith)
import Sidepanel.Routing (Route(..), parseRoute, printRoute)

-- Child slots for each view
type ChildSlots =
  ( dashboard :: H.Slot Query Void Unit
  , session :: H.Slot Query Void Unit
  , files :: H.Slot Query Void Unit
  , diff :: H.Slot Query Void Unit
  , proofs :: H.Slot Query Void Unit
  , timeline :: H.Slot Query Void Unit
  , recordings :: H.Slot Query Void Unit
  , search :: H.Slot Query Void Unit
  , performance :: H.Slot Query Void Unit
  , settings :: H.Slot Query Void Unit
  )

type State =
  { currentRoute :: Route
  , previousRoute :: Maybe Route
  , isNavigating :: Boolean
  }

data Action
  = Initialize
  | Navigate Route
  | HandleHashChange String
  | GoBack
  | GoForward

data Query a
  = NavigateQ Route a
  | GetCurrentRoute (Route -> a)

component :: forall i o m. MonadAff m => H.Component Query i o m
component = H.mkComponent
  { initialState: const { currentRoute: Dashboard, previousRoute: Nothing, isNavigating: false }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , initialize = Just Initialize
      }
  }

render :: forall m. MonadAff m => State -> H.ComponentHTML Action ChildSlots m
render state =
  HH.div
    [ HP.class_ (H.ClassName "router") ]
    [ renderCurrentView state.currentRoute ]

renderCurrentView :: forall m. MonadAff m => Route -> H.ComponentHTML Action ChildSlots m
renderCurrentView = case _ of
  Dashboard ->
    HH.slot (Proxy :: _ "dashboard") unit Dashboard.component {} absurd
  
  Session route ->
    HH.slot (Proxy :: _ "session") unit Session.component { route } absurd
  
  Files ->
    HH.slot (Proxy :: _ "files") unit FileContext.component {} absurd
  
  Diff ->
    HH.slot (Proxy :: _ "diff") unit DiffViewer.component {} absurd
  
  Proofs route ->
    HH.slot (Proxy :: _ "proofs") unit Proofs.component { route } absurd
  
  Timeline snapshotId ->
    HH.slot (Proxy :: _ "timeline") unit Timeline.component { snapshotId } absurd
  
  Recordings recordingId ->
    HH.slot (Proxy :: _ "recordings") unit Recordings.component { recordingId } absurd
  
  Search query ->
    HH.slot (Proxy :: _ "search") unit Search.component { query } absurd
  
  Performance ->
    HH.slot (Proxy :: _ "performance") unit Performance.component {} absurd
  
  Settings section ->
    HH.slot (Proxy :: _ "settings") unit Settings.component { section } absurd
  
  NotFound path ->
    HH.div
      [ HP.class_ (H.ClassName "not-found") ]
      [ HH.text $ "Page not found: " <> path ]

handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action ChildSlots o m Unit
handleAction = case _ of
  Initialize -> do
    -- Subscribe to hash changes
    void $ H.subscribe $ hashChangeEmitter HandleHashChange
    
    -- Parse initial route
    hash <- H.liftEffect getHash
    let route = parseRoute hash
    H.modify_ _ { currentRoute = route }
  
  Navigate route -> do
    current <- H.gets _.currentRoute
    when (route /= current) do
      H.modify_ _ { previousRoute = Just current, isNavigating = true }
      H.liftEffect $ setHash (printRoute route)
      H.modify_ _ { currentRoute = route, isNavigating = false }
  
  HandleHashChange hash -> do
    let route = parseRoute hash
    H.modify_ \s -> s 
      { previousRoute = Just s.currentRoute
      , currentRoute = route 
      }
  
  GoBack ->
    H.liftEffect historyBack
  
  GoForward ->
    H.liftEffect historyForward

handleQuery :: forall o m a. MonadAff m 
            => Query a -> H.HalogenM State Action ChildSlots o m (Maybe a)
handleQuery = case _ of
  NavigateQ route next -> do
    handleAction (Navigate route)
    pure $ Just next
  
  GetCurrentRoute reply -> do
    route <- H.gets _.currentRoute
    pure $ Just (reply route)
```

---

## Navigation Helpers

```purescript
module Sidepanel.Navigation where

import Prelude
import Effect (Effect)
import Sidepanel.Routing (Route(..))

-- Navigation functions
navigateTo :: Route -> Effect Unit
navigateTo route = setHash (printRoute route)

-- Convenience functions
goToDashboard :: Effect Unit
goToDashboard = navigateTo Dashboard

goToSession :: String -> Effect Unit
goToSession id = navigateTo (Session (Just (SpecificSession id)))

goToMessage :: String -> String -> Effect Unit
goToMessage sessionId msgId = navigateTo (Session (Just (SessionMessage sessionId msgId)))

goToProofFile :: String -> Effect Unit
goToProofFile file = navigateTo (Proofs (Just (ProofFile file)))

goToSnapshot :: String -> Effect Unit
goToSnapshot id = navigateTo (Timeline (Just id))

goToRecording :: String -> Effect Unit
goToRecording id = navigateTo (Recordings (Just id))

searchFor :: String -> Effect Unit
searchFor query = navigateTo (Search (Just query))

-- Link builder for HTML
routeToHref :: Route -> String
routeToHref = ("#" <> _) <<< printRoute
```

---

## Keyboard Navigation

```purescript
-- Keyboard shortcuts for routes
routeShortcuts :: Map String Route
routeShortcuts = Map.fromFoldable
  [ Tuple "1" Dashboard
  , Tuple "2" (Session Nothing)
  , Tuple "3" (Proofs Nothing)
  , Tuple "4" (Timeline Nothing)
  , Tuple "5" (Settings Nothing)
  , Tuple "g d" Dashboard
  , Tuple "g s" (Session Nothing)
  , Tuple "g p" (Proofs Nothing)
  , Tuple "g t" (Timeline Nothing)
  , Tuple "g f" Files
  , Tuple "g r" (Recordings Nothing)
  , Tuple "/" (Search Nothing)
  ]

handleKeyboardNavigation :: String -> Maybe Route
handleKeyboardNavigation key = Map.lookup key routeShortcuts
```

---

## Deep Linking

### Sharing Links

```purescript
-- Generate shareable link
generateShareLink :: Route -> Effect String
generateShareLink route = do
  origin <- getWindowOrigin
  pure $ origin <> "/#" <> printRoute route

-- Copy link to clipboard
shareCurrentRoute :: Route -> Effect Unit
shareCurrentRoute route = do
  link <- generateShareLink route
  copyToClipboard link
```

### Opening from External

```purescript
-- Handle opening from external link (e.g., notification)
handleExternalLink :: String -> Effect Unit
handleExternalLink url = do
  let hash = extractHash url
  let route = parseRoute hash
  navigateTo route
```

---

## Route Guards

```purescript
-- Check if route requires authentication
requiresAuth :: Route -> Boolean
requiresAuth = case _ of
  Settings _ -> true
  _ -> false

-- Check if route requires active session
requiresSession :: Route -> Boolean
requiresSession = case _ of
  Session (Just (SpecificSession _)) -> true
  Session (Just (SessionMessage _ _)) -> true
  _ -> false

-- Route guard middleware
withRouteGuard :: forall m. MonadAff m 
               => Route -> m Unit -> m Unit
withRouteGuard route action = do
  hasSession <- checkHasSession
  
  if requiresSession route && not hasSession
    then navigateTo (Session Nothing)
    else action
```

---

## Browser History FFI

```javascript
// frontend/src/Sidepanel/FFI/History.js

export function getHash() {
  return window.location.hash.slice(1) || '/';
}

export function setHash(hash) {
  return function() {
    window.location.hash = hash;
  };
}

export function historyBack() {
  window.history.back();
}

export function historyForward() {
  window.history.forward();
}

export function pushState(url) {
  return function() {
    window.history.pushState(null, '', url);
  };
}

export function replaceState(url) {
  return function() {
    window.history.replaceState(null, '', url);
  };
}

// Hash change emitter for Halogen subscriptions
export function hashChangeEmitter(handler) {
  return function(emit) {
    const listener = function() {
      emit(handler(getHash()))();
    };
    window.addEventListener('hashchange', listener);
    
    return function() {
      window.removeEventListener('hashchange', listener);
    };
  };
}
```

---

## CSS Transitions

```css
/* Route transition animations */
.router {
  position: relative;
  width: 100%;
  height: 100%;
}

.router > * {
  animation: fadeIn 0.15s ease-out;
}

@keyframes fadeIn {
  from {
    opacity: 0;
    transform: translateY(4px);
  }
  to {
    opacity: 1;
    transform: translateY(0);
  }
}

/* For lateral navigation (between peer views) */
.router--slide-left > * {
  animation: slideInLeft 0.2s ease-out;
}

.router--slide-right > * {
  animation: slideInRight 0.2s ease-out;
}

@keyframes slideInLeft {
  from {
    opacity: 0;
    transform: translateX(20px);
  }
  to {
    opacity: 1;
    transform: translateX(0);
  }
}

@keyframes slideInRight {
  from {
    opacity: 0;
    transform: translateX(-20px);
  }
  to {
    opacity: 1;
    transform: translateX(0);
  }
}
```

---

## Related Specifications

- `48-KEYBOARD-NAVIGATION.md` - Keyboard shortcuts
- `49-SIDEBAR-NAVIGATION.md` - Sidebar component
- `66-SEARCH-VIEW.md` - Search navigation

---

*"Navigation should be instant, intuitive, and keyboard-friendly."*
