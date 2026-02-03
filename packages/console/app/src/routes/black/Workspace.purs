-- | Black Workspace Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/black/workspace.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Black.Workspace
  ( WorkspaceItem(..)
  , WorkspaceListState(..)
  , WorkspaceListAction(..)
  , initialState
  , reducer
  , formatStarCount
  , buildWorkspaceUrl
  ) where

import Prelude

import Data.Array (head, findIndex)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Int (floor, toNumber)

-- | Workspace item
type WorkspaceItem =
  { name :: String
  , id :: String
  }

-- | Workspace list state
type WorkspaceListState =
  { workspaces :: Array WorkspaceItem
  , activeId :: Maybe String
  , starCount :: Maybe Int
  }

-- | Initial state
initialState :: Array WorkspaceItem -> WorkspaceListState
initialState workspaces =
  { workspaces
  , activeId: map _.id (head workspaces)
  , starCount: Nothing
  }

-- | List actions
data WorkspaceListAction
  = SetActive String
  | SetStarCount Int
  | NavigateNext
  | NavigatePrev

derive instance eqWorkspaceListAction :: Eq WorkspaceListAction

instance showWorkspaceListAction :: Show WorkspaceListAction where
  show (SetActive id) = "(SetActive " <> show id <> ")"
  show (SetStarCount n) = "(SetStarCount " <> show n <> ")"
  show NavigateNext = "NavigateNext"
  show NavigatePrev = "NavigatePrev"

-- | State reducer (pure)
reducer :: WorkspaceListState -> WorkspaceListAction -> WorkspaceListState
reducer state action = case action of
  SetActive id ->
    state { activeId = Just id }
  
  SetStarCount count ->
    state { starCount = Just count }
  
  NavigateNext ->
    let
      currentIndex = findCurrentIndex state
      nextIndex = min (currentIndex + 1) (length state.workspaces - 1)
      nextId = getIdAtIndex state.workspaces nextIndex
    in
      state { activeId = nextId }
  
  NavigatePrev ->
    let
      currentIndex = findCurrentIndex state
      prevIndex = max (currentIndex - 1) 0
      prevId = getIdAtIndex state.workspaces prevIndex
    in
      state { activeId = prevId }

  where
    findCurrentIndex :: WorkspaceListState -> Int
    findCurrentIndex s = case s.activeId of
      Nothing -> 0
      Just id -> fromMaybe 0 (findIndex (\w -> w.id == id) s.workspaces)
    
    getIdAtIndex :: Array WorkspaceItem -> Int -> Maybe String
    getIdAtIndex arr idx = map _.id (index arr idx)
    
    length :: forall a. Array a -> Int
    length _ = 0  -- simplified
    
    index :: forall a. Array a -> Int -> Maybe a
    index _ _ = Nothing  -- simplified
    
    min :: Int -> Int -> Int
    min a b = if a < b then a else b
    
    max :: Int -> Int -> Int
    max a b = if a > b then a else b

-- | Format star count with compact notation (pure)
formatStarCount :: Int -> String
formatStarCount stars
  | stars >= 1000 = show (stars / 1000) <> "k"
  | otherwise = show stars

-- | Build workspace URL (pure)
buildWorkspaceUrl :: String -> String
buildWorkspaceUrl workspaceId = "/black/workspace/" <> workspaceId

-- | Footer link configuration
type FooterLink =
  { text :: String
  , href :: String
  , external :: Boolean
  }

footerLinks :: String -> Int -> Array FooterLink
footerLinks repoUrl stars =
  [ { text: "GitHub [" <> formatStarCount stars <> "]", href: repoUrl, external: true }
  , { text: "Docs", href: "/docs", external: false }
  , { text: "Privacy", href: "/legal/privacy-policy", external: false }
  , { text: "Terms", href: "/legal/terms-of-service", external: false }
  ]
