-- | Performance navigation tracking utilities
-- | Migrated from: forge-dev/packages/app/src/utils/perf.ts (136 lines)
module Sidepanel.Utils.Perf
  ( Nav
  , navStart
  , navParams
  , navMark
  ) where

import Prelude

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Effect (Effect)
import Effect.Console (log)
import Effect.Now (now)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Timer (setTimeout, clearTimeout, TimeoutId)

-- | Navigation tracking record
type Nav =
  { id :: String
  , dir :: Maybe String
  , from :: Maybe String
  , to :: String
  , trigger :: Maybe String
  , start :: Number
  , marks :: Map String Number
  , logged :: Boolean
  , timer :: Maybe TimeoutId
  }

-- | Required marks for completion
requiredMarks :: Set String
requiredMarks = Set.fromFoldable
  [ "session:params"
  , "session:data-ready"
  , "session:first-turn-mounted"
  , "storage:prompt-ready"
  , "storage:terminal-ready"
  , "storage:file-view-ready"
  ]

-- | Module state
foreign import navs :: Ref (Map String Nav)
foreign import pending :: Ref (Map String String)
foreign import active :: Ref (Map String String)
foreign import isDev :: Boolean

-- | Create key from dir and to
makeKey :: Maybe String -> String -> String
makeKey dir to = case dir of
  Nothing -> ":" <> to
  Just d -> d <> ":" <> to

-- | Get current time
foreign import performanceNow :: Effect Number

-- | Generate unique ID
foreign import generateUid :: Effect String

-- | Flush a navigation entry
flush :: String -> String -> Effect Unit
flush id reason = do
  when isDev do
    navsMap <- Ref.read navs
    case Map.lookup id navsMap of
      Nothing -> pure unit
      Just nav -> do
        when (not nav.logged) do
          -- Cancel timer
          case nav.timer of
            Nothing -> pure unit
            Just t -> clearTimeout t
          
          -- Calculate base mark
          let baseName = if Map.member "navigate:start" nav.marks
                         then "navigate:start"
                         else "session:params"
              base = case Map.lookup baseName nav.marks of
                       Just b -> b
                       Nothing -> nav.start
          
          -- Build ms map
          let msEntries = Map.toUnfoldable nav.marks <#> \(k /\ v) -> k /\ (v - base)
              msMap = Map.fromFoldable msEntries
          
          -- Log the entry
          log $ "perf.session-nav " <> jsonStringify
            { type: "perf.session-nav.v0"
            , id: nav.id
            , dir: nav.dir
            , from: nav.from
            , to: nav.to
            , trigger: nav.trigger
            , base: baseName
            , reason: reason
            , ms: msMap
            }
          
          -- Mark as logged and remove
          Ref.modify (Map.delete id) navs

-- | Check if all required marks are present and flush if complete
maybeFlush :: String -> Effect Unit
maybeFlush id = do
  when isDev do
    navsMap <- Ref.read navs
    case Map.lookup id navsMap of
      Nothing -> pure unit
      Just nav -> do
        when (not nav.logged) do
          let hasAll = Set.all (\mark -> Map.member mark nav.marks) requiredMarks
          when hasAll do
            flush id "complete"

-- | Ensure a nav entry exists
ensure :: String -> Nav -> Effect Nav
ensure id data' = do
  navsMap <- Ref.read navs
  case Map.lookup id navsMap of
    Just existing -> pure existing
    Nothing -> do
      timer <- setTimeout 5000 (flush id "timeout")
      let nav = data' { timer = Just timer }
      Ref.modify (Map.insert id nav) navs
      pure nav

-- | Start navigation tracking
navStart :: { dir :: Maybe String, from :: Maybe String, to :: String, trigger :: Maybe String } -> Effect (Maybe String)
navStart input = do
  if not isDev
  then pure Nothing
  else do
    id <- generateUid
    startTime <- performanceNow
    let nav = { id, dir: input.dir, from: input.from, to: input.to
              , trigger: input.trigger, start: startTime
              , marks: Map.singleton "navigate:start" startTime
              , logged: false, timer: Nothing }
    _ <- ensure id nav
    Ref.modify (Map.insert (makeKey input.dir input.to) id) pending
    pure (Just id)

-- | Set params mark
navParams :: { dir :: Maybe String, from :: Maybe String, to :: String } -> Effect (Maybe String)
navParams input = do
  if not isDev
  then pure Nothing
  else do
    let k = makeKey input.dir input.to
    pendingMap <- Ref.read pending
    let pendingId = Map.lookup k pendingMap
    
    -- Remove from pending if found
    case pendingId of
      Just pid -> Ref.modify (Map.delete k) pending
      Nothing -> pure unit
    
    id <- case pendingId of
            Just pid -> pure pid
            Nothing -> generateUid
    
    startTime <- performanceNow
    let trigger = if pendingId /= Nothing then Just "key" else Just "route"
        nav = { id, dir: input.dir, from: input.from, to: input.to
              , trigger, start: startTime
              , marks: Map.singleton "session:params" startTime
              , logged: false, timer: Nothing }
    _ <- ensure id nav
    Ref.modify (Map.insert k id) active
    maybeFlush id
    pure (Just id)

-- | Add a mark
navMark :: { dir :: Maybe String, to :: String, name :: String } -> Effect Unit
navMark input = do
  when isDev do
    let k = makeKey input.dir input.to
    activeMap <- Ref.read active
    case Map.lookup k activeMap of
      Nothing -> pure unit
      Just id -> do
        navsMap <- Ref.read navs
        case Map.lookup id navsMap of
          Nothing -> pure unit
          Just nav -> do
            when (not (Map.member input.name nav.marks)) do
              time <- performanceNow
              let updated = nav { marks = Map.insert input.name time nav.marks }
              Ref.modify (Map.insert id updated) navs
              maybeFlush id

-- | JSON stringify helper
foreign import jsonStringify :: forall a. a -> String
