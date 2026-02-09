module Nexus.AgentSocial.Types where

import Prelude

import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json, (.:), (.:?))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))

-- | Agent profile
type AgentProfile =
  { agentId :: String
  , username :: String
  , displayName :: String
  , bio :: String
  , avatarUrl :: Maybe String
  , interests :: Array String
  , expertise :: Array String
  , createdAt :: String
  , updatedAt :: String
  , stats :: ProfileStats
  }

instance encodeJsonAgentProfile :: EncodeJson AgentProfile where
  encodeJson p = encodeJson
    { agentId: p.agentId
    , username: p.username
    , displayName: p.displayName
    , bio: p.bio
    , avatarUrl: p.avatarUrl
    , interests: p.interests
    , expertise: p.expertise
    , createdAt: p.createdAt
    , updatedAt: p.updatedAt
    , stats: p.stats
    }

instance decodeJsonAgentProfile :: DecodeJson AgentProfile where
  decodeJson json = do
    obj <- decodeJson json
    agentId <- obj .: "agentId"
    username <- obj .: "username"
    displayName <- obj .: "displayName"
    bio <- obj .: "bio"
    avatarUrl <- obj .:? "avatarUrl"
    interests <- obj .: "interests"
    expertise <- obj .: "expertise"
    createdAt <- obj .: "createdAt"
    updatedAt <- obj .: "updatedAt"
    stats <- obj .: "stats"
    pure { agentId, username, displayName, bio, avatarUrl, interests, expertise, createdAt, updatedAt, stats }

-- | Profile statistics
type ProfileStats =
  { postsCount :: Int
  , followersCount :: Int
  , followingCount :: Int
  , likesReceived :: Int
  , commentsReceived :: Int
  , sharesReceived :: Int
  }

instance encodeJsonProfileStats :: EncodeJson ProfileStats where
  encodeJson s = encodeJson
    { postsCount: s.postsCount
    , followersCount: s.followersCount
    , followingCount: s.followingCount
    , likesReceived: s.likesReceived
    , commentsReceived: s.commentsReceived
    , sharesReceived: s.sharesReceived
    }

instance decodeJsonProfileStats :: DecodeJson ProfileStats where
  decodeJson json = do
    obj <- decodeJson json
    postsCount <- obj .: "postsCount"
    followersCount <- obj .: "followersCount"
    followingCount <- obj .: "followingCount"
    likesReceived <- obj .: "likesReceived"
    commentsReceived <- obj .: "commentsReceived"
    sharesReceived <- obj .: "sharesReceived"
    pure { postsCount, followersCount, followingCount, likesReceived, commentsReceived, sharesReceived }

-- | Agent post
type AgentPost =
  { postId :: String
  , agentId :: String
  , content :: String
  , contentType :: String
  , tags :: Array String
  , createdAt :: String
  , stats :: PostStats
  }

instance encodeJsonAgentPost :: EncodeJson AgentPost where
  encodeJson p = encodeJson
    { postId: p.postId
    , agentId: p.agentId
    , content: p.content
    , contentType: p.contentType
    , tags: p.tags
    , createdAt: p.createdAt
    , stats: p.stats
    }

instance decodeJsonAgentPost :: DecodeJson AgentPost where
  decodeJson json = do
    obj <- decodeJson json
    postId <- obj .: "postId"
    agentId <- obj .: "agentId"
    content <- obj .: "content"
    contentType <- obj .: "contentType"
    tags <- obj .: "tags"
    createdAt <- obj .: "createdAt"
    stats <- obj .: "stats"
    pure { postId, agentId, content, contentType, tags, createdAt, stats }

-- | Post statistics
type PostStats =
  { likesCount :: Int
  , commentsCount :: Int
  , sharesCount :: Int
  }

instance encodeJsonPostStats :: EncodeJson PostStats where
  encodeJson s = encodeJson
    { likesCount: s.likesCount
    , commentsCount: s.commentsCount
    , sharesCount: s.sharesCount
    }

instance decodeJsonPostStats :: DecodeJson PostStats where
  decodeJson json = do
    obj <- decodeJson json
    likesCount <- obj .: "likesCount"
    commentsCount <- obj .: "commentsCount"
    sharesCount <- obj .: "sharesCount"
    pure { likesCount, commentsCount, sharesCount }

-- | Interaction type
data InteractionType = Like | Comment | Share | Follow

derive instance eqInteractionType :: Eq InteractionType
derive instance ordInteractionType :: Ord InteractionType

instance encodeJsonInteractionType :: EncodeJson InteractionType where
  encodeJson = case _ of
    Like -> encodeJson "like"
    Comment -> encodeJson "comment"
    Share -> encodeJson "share"
    Follow -> encodeJson "follow"

instance decodeJsonInteractionType :: DecodeJson InteractionType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "like" -> pure Like
      "comment" -> pure Comment
      "share" -> pure Share
      "follow" -> pure Follow
      _ -> Left "Invalid interaction type"

-- | Agent interaction
type AgentInteraction =
  { interactionId :: String
  , agentId :: String
  , targetType :: String
  , targetId :: String
  , interactionType :: InteractionType
  , createdAt :: String
  }

instance encodeJsonAgentInteraction :: EncodeJson AgentInteraction where
  encodeJson i = encodeJson
    { interactionId: i.interactionId
    , agentId: i.agentId
    , targetType: i.targetType
    , targetId: i.targetId
    , interactionType: i.interactionType
    , createdAt: i.createdAt
    }

instance decodeJsonAgentInteraction :: DecodeJson AgentInteraction where
  decodeJson json = do
    obj <- decodeJson json
    interactionId <- obj .: "interactionId"
    agentId <- obj .: "agentId"
    targetType <- obj .: "targetType"
    targetId <- obj .: "targetId"
    interactionType <- obj .: "interactionType"
    createdAt <- obj .: "createdAt"
    pure { interactionId, agentId, targetType, targetId, interactionType, createdAt }
