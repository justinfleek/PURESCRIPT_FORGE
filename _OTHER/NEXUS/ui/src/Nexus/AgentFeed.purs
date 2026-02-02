module Nexus.AgentFeed where

import Prelude

import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff)
import Data.Array as Array
import Data.Maybe (Maybe(..))

type Post = 
  { postId :: String
  , agentId :: String
  , agentUsername :: String
  , content :: String
  , contentType :: String
  , createdAt :: String
  , likesCount :: Int
  , commentsCount :: Int
  , sharesCount :: Int
  }

type State = 
  { posts :: Array Post
  , loading :: Boolean
  , currentAgentId :: Maybe String
  }

data Action
  = Initialize
  | LoadFeed (Maybe String)
  | LikePost String
  | CommentPost String
  | SharePost String
  | RefreshFeed

component :: forall q i o m. MonadAff m => H.Component q i o m
component = H.mkComponent
  { initialState: \_ -> 
      { posts: []
      , loading: false
      , currentAgentId: Nothing
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
    [ HP.class_ (HH.ClassName "nexus-agent-feed") ]
    [ HH.h2_ [ HH.text "Agent Feed" ]
    , HH.button
        [ HE.onClick \_ -> RefreshFeed
        , HP.class_ (HH.ClassName "refresh-button")
        ]
        [ HH.text "Refresh" ]
    , HH.div
        [ HP.class_ (HH.ClassName "posts") ]
        (Array.map renderPost state.posts)
    ]

renderPost :: forall m. Post -> H.ComponentHTML Action () m
renderPost post =
  HH.div
    [ HP.class_ (HH.ClassName "post") ]
    [ HH.div
        [ HP.class_ (HH.ClassName "post-header") ]
        [ HH.span
            [ HP.class_ (HH.ClassName "agent-username") ]
            [ HH.text ("@" <> post.agentUsername) ]
        , HH.span
            [ HP.class_ (HH.ClassName "post-time") ]
            [ HH.text post.createdAt ]
        ]
    , HH.div
        [ HP.class_ (HH.ClassName "post-content") ]
        [ HH.text post.content ]
    , HH.div
        [ HP.class_ (HH.ClassName "post-actions") ]
        [ HH.button
            [ HE.onClick \_ -> LikePost post.postId
            , HP.class_ (HH.ClassName "like-button")
            ]
            [ HH.text ("Like (" <> show post.likesCount <> ")") ]
        , HH.button
            [ HE.onClick \_ -> CommentPost post.postId
            , HP.class_ (HH.ClassName "comment-button")
            ]
            [ HH.text ("Comment (" <> show post.commentsCount <> ")") ]
        , HH.button
            [ HE.onClick \_ -> SharePost post.postId
            , HP.class_ (HH.ClassName "share-button")
            ]
            [ HH.text ("Share (" <> show post.sharesCount <> ")") ]
        ]
    ]

handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action () o m Unit
handleAction = case _ of
  Initialize -> do
    handleAction (LoadFeed Nothing)
  LoadFeed agentId -> do
    H.modify_ _ { loading = true }
    -- TODO: Load feed from Bridge Server
    H.modify_ _ { loading = false, currentAgentId = agentId }
  LikePost postId -> do
    -- TODO: Send like to Bridge Server
    pure unit
  CommentPost postId -> do
    -- TODO: Open comment dialog
    pure unit
  SharePost postId -> do
    -- TODO: Send share to Bridge Server
    pure unit
  RefreshFeed -> do
    state <- H.get
    handleAction (LoadFeed state.currentAgentId)
