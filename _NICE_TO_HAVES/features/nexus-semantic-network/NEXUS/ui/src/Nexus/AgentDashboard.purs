module Nexus.AgentDashboard where

import Prelude

import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff)
import Data.Maybe (Maybe(..))
import Data.Array as Array

type Agent = 
  { id :: String
  , username :: String
  , displayName :: String
  , status :: String
  , agentType :: String
  }

type State = 
  { agents :: Array Agent
  , selectedAgent :: Maybe String
  , loading :: Boolean
  }

data Action
  = Initialize
  | SelectAgent String
  | RefreshAgents
  | LoadAgents

component :: forall q i o. MonadAff m => H.Component q i o m
component = H.mkComponent
  { initialState: \_ -> 
      { agents: []
      , selectedAgent: Nothing
      , loading: false
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state = 
  HH.div
    [ HP.class_ (HH.ClassName "nexus-agent-dashboard") ]
    [ HH.h1_ [ HH.text "Nexus Agent Dashboard" ]
    , HH.div
        [ HP.class_ (HH.ClassName "agent-list") ]
        (Array.map renderAgent state.agents)
    , HH.button
        [ HE.onClick \_ -> RefreshAgents
        , HP.class_ (HH.ClassName "refresh-button")
        ]
        [ HH.text "Refresh" ]
    ]

renderAgent :: forall m. Agent -> H.ComponentHTML Action () m
renderAgent agent =
  HH.div
    [ HP.class_ (HH.ClassName "agent-item")
    , HE.onClick \_ -> SelectAgent agent.id
    ]
    [ HH.h3_ [ HH.text agent.displayName ]
    , HH.p_ [ HH.text ("@" <> agent.username) ]
    , HH.span
        [ HP.class_ (HH.ClassName ("status-" <> agent.status)) ]
        [ HH.text agent.status ]
    , HH.span
        [ HP.class_ (HH.ClassName "agent-type") ]
        [ HH.text agent.agentType ]
    ]

handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action () o m Unit
handleAction = case _ of
  Initialize -> do
    handleAction LoadAgents
  SelectAgent agentId -> do
    H.modify_ _ { selectedAgent = Just agentId }
  RefreshAgents -> do
    handleAction LoadAgents
  LoadAgents -> do
    H.modify_ _ { loading = true }
    -- TODO: Load agents from Bridge Server
    H.modify_ _ { loading = false }
