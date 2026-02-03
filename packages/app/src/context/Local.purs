-- | Local context - manages local session state (agent, model selection)
-- | Migrated from: forge-dev/packages/app/src/context/local.tsx
module App.Context.Local
  ( ModelKey
  , LocalState
  , AgentState
  , mkLocalState
  , getCurrentAgent
  , setAgent
  , cycleAgent
  , getCurrentModel
  , setModel
  , cycleModel
  , isModelValid
  ) where

import Prelude

import Data.Array (elem, filter, findIndex, head, length, (!!))
import Data.Maybe (Maybe(..), fromMaybe)

-- | Model key
type ModelKey =
  { providerID :: String
  , modelID :: String
  }

-- | Agent info
type AgentInfo =
  { name :: String
  , mode :: Maybe String
  , hidden :: Boolean
  , model :: Maybe ModelKey
  }

-- | Agent state
type AgentState =
  { list :: Array AgentInfo
  , current :: Maybe String
  }

-- | Local state
type LocalState =
  { agent :: AgentState
  , ephemeralModel :: Maybe ModelKey
  }

-- | Create initial local state
mkLocalState :: LocalState
mkLocalState =
  { agent: { list: [], current: Nothing }
  , ephemeralModel: Nothing
  }

-- | Get visible agents (not subagent, not hidden)
visibleAgents :: AgentState -> Array AgentInfo
visibleAgents state =
  filter (\a -> a.mode /= Just "subagent" && not a.hidden) state.list

-- | Get current agent
getCurrentAgent :: LocalState -> Maybe AgentInfo
getCurrentAgent state =
  let
    available = visibleAgents state.agent
  in
    case state.agent.current of
      Nothing -> head available
      Just name ->
        case filter (\a -> a.name == name) available of
          [] -> head available
          (a : _) -> Just a

-- | Set current agent
setAgent :: String -> LocalState -> LocalState
setAgent name state =
  let
    available = visibleAgents state.agent
    agentState = state.agent
  in
    if length available == 0
    then state { agent = agentState { current = Nothing } }
    else
      let
        exists = available # filter (\a -> a.name == name) # length # (_ > 0)
      in
        if exists
        then state { agent = agentState { current = Just name } }
        else state { agent = agentState { current = map _.name (head available) } }

-- | Cycle to next/previous agent
cycleAgent :: Int -> LocalState -> LocalState
cycleAgent direction state =
  let
    available = visibleAgents state.agent
    len = length available
  in
    if len == 0
    then state { agent = state.agent { current = Nothing } }
    else
      let
        currentIdx = case state.agent.current of
          Nothing -> 0
          Just name ->
            fromMaybe 0 (findIndex (\a -> a.name == name) available)
        nextIdx = (currentIdx + direction + len) `mod` len
        nextAgent = available !! nextIdx
      in
        case nextAgent of
          Nothing -> state
          Just a -> state { agent = state.agent { current = Just a.name } }

-- | Check if model is valid (exists and provider is connected)
isModelValid :: ModelKey -> Array { id :: String, models :: Array String } -> Array String -> Boolean
isModelValid model providers connected =
  let
    providerConnected = elem model.providerID connected
    modelExists = providers
      # filter (\p -> p.id == model.providerID)
      # head
      # map (\p -> elem model.modelID p.models)
      # fromMaybe false
  in
    providerConnected && modelExists

-- | Get current model
getCurrentModel :: LocalState -> Maybe ModelKey
getCurrentModel state =
  case state.ephemeralModel of
    Just m -> Just m
    Nothing ->
      case getCurrentAgent state of
        Nothing -> Nothing
        Just a -> a.model

-- | Set current model
setModel :: Maybe ModelKey -> LocalState -> LocalState
setModel model state = state { ephemeralModel = model }

-- | Cycle through recent models
cycleModel :: Int -> Array ModelKey -> LocalState -> LocalState
cycleModel direction recent state =
  let
    len = length recent
  in
    if len == 0
    then state
    else
      case state.ephemeralModel of
        Nothing ->
          case head recent of
            Nothing -> state
            Just m -> state { ephemeralModel = Just m }
        Just current ->
          let
            currentIdx = fromMaybe 0 (findIndex (\m -> m.providerID == current.providerID && m.modelID == current.modelID) recent)
            nextIdx = (currentIdx + direction + len) `mod` len
          in
            case recent !! nextIdx of
              Nothing -> state
              Just m -> state { ephemeralModel = Just m }
