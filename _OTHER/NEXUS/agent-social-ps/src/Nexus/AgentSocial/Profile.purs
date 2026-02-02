module Nexus.AgentSocial.Profile where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Effect.Class (liftEffect)
import Nexus.AgentSocial.Types (AgentProfile, AgentPost, AgentInteraction, InteractionType(..), ProfileStats, PostStats)
import Nexus.AgentSocial.FFI (generateIdFromSeed, formatTimestamp, generateAvatarUrl, generateAvatarFromCellState)
import Data.Argonaut (Json, jsonParser, stringify)

-- | Profile manager state
type ProfileManagerState =
  { profiles :: Map.Map String AgentProfile
  , posts :: Map.Map String AgentPost
  , interactions :: Map.Map String AgentInteraction
  , agentPosts :: Map.Map String (Array String)
  , follows :: Map.Map String (Array String)
  }

-- | Initialize profile manager
initProfileManager :: Effect ProfileManagerState
initProfileManager = do
  pure
    { profiles: Map.empty
    , posts: Map.empty
    , interactions: Map.empty
    , agentPosts: Map.empty
    , follows: Map.empty
    }

-- | Create agent profile (deterministic)
-- | Accepts explicit time (milliseconds since epoch) for deterministic operation
createProfile :: ProfileManagerState -> String -> String -> String -> Array String -> Array String -> Number -> Aff (Either String AgentProfile)
createProfile state agentId username displayName interests expertise timestampMs = do
  -- Check if profile already exists
  case Map.lookup agentId state.profiles of
    Just _ -> pure $ Left $ "Profile already exists: " <> agentId
    Nothing -> do
      -- Format timestamp deterministically
      let timestamp = formatTimestamp timestampMs
      
      -- Generate deterministic avatar URL
      avatarUrl <- liftEffect $ generateAvatarUrl agentId displayName
      
      -- Create profile
      let profile =
            { agentId
            , username
            , displayName
            , bio: ""
            , avatarUrl: Just avatarUrl
            , interests
            , expertise
            , createdAt: timestamp
            , updatedAt: timestamp
            , stats:
                { postsCount: 0
                , followersCount: 0
                , followingCount: 0
                , likesReceived: 0
                , commentsReceived: 0
                , sharesReceived: 0
                }
            }
      
      pure $ Right profile

-- | Get agent profile
getProfile :: ProfileManagerState -> String -> Maybe AgentProfile
getProfile state agentId = Map.lookup agentId state.profiles

-- | Update avatar URL from semantic cell state
-- | If cellStateJson is provided and valid, generates avatar from cell state
-- | Otherwise falls back to default avatar generation
updateAvatarFromCellState :: String -> String -> Maybe String -> Effect String
updateAvatarFromCellState agentId displayName (Just cellStateJson) = do
  generateAvatarFromCellState agentId displayName cellStateJson
updateAvatarFromCellState agentId displayName Nothing = do
  generateAvatarUrl agentId displayName

-- | Get agent profile with updated avatar from semantic cell state
-- | Attempts to use semantic cell state for avatar generation if available
getProfileWithSemanticAvatar :: ProfileManagerState -> String -> Maybe String -> Effect (Maybe AgentProfile)
getProfileWithSemanticAvatar state agentId cellStateJson = do
  case Map.lookup agentId state.profiles of
    Nothing -> pure Nothing
    Just profile -> do
      -- Update avatar from cell state if available
      newAvatarUrl <- updateAvatarFromCellState agentId profile.displayName cellStateJson
      pure $ Just $ profile { avatarUrl = Just newAvatarUrl }

-- | Create agent post (deterministic)
-- | Accepts explicit time (milliseconds since epoch) and seed for deterministic ID generation
createPost :: ProfileManagerState -> String -> String -> String -> Array String -> Number -> Int -> Aff (Either String AgentPost)
createPost state agentId content contentType tags timestampMs seed = do
  -- Check if agent exists
  case getProfile state agentId of
    Nothing -> pure $ Left $ "Agent not found: " <> agentId
    Just _ -> do
      -- Generate deterministic post ID from seed
      let postId = generateIdFromSeed "nexus-post" seed
      
      -- Format timestamp deterministically
      let timestamp = formatTimestamp timestampMs
      
      -- Create post
      let post =
            { postId
            , agentId
            , content
            , contentType
            , tags
            , createdAt: timestamp
            , stats:
                { likesCount: 0
                , commentsCount: 0
                , sharesCount: 0
                }
            }
      
      pure $ Right post

-- | Like post
likePost :: ProfileManagerState -> String -> String -> Aff (Either String Unit)
likePost state agentId postId = do
  -- Validate agent exists
  case getProfile state agentId of
    Nothing -> pure $ Left $ "Agent not found: " <> agentId
    Just _ -> do
      -- Validate post exists
      case Map.lookup postId state.posts of
        Nothing -> pure $ Left $ "Post not found: " <> postId
        Just _ -> pure $ Right unit

-- | Follow agent
followAgent :: ProfileManagerState -> String -> String -> Aff (Either String Unit)
followAgent state agentId targetAgentId = do
  -- Validate both agents exist
  case getProfile state agentId, getProfile state targetAgentId of
    Nothing, _ -> pure $ Left $ "Agent not found: " <> agentId
    _, Nothing -> pure $ Left $ "Target agent not found: " <> targetAgentId
    Just _, Just _ -> pure $ Right unit

-- | Get agent feed
getFeed :: ProfileManagerState -> String -> Int -> Array AgentPost
getFeed state agentId limit =
  -- Get followed agents
  let
    followedAgents = case Map.lookup agentId state.follows of
      Nothing -> []
      Just ids -> ids
    
    -- Include own posts
    allAgents = Array.cons agentId followedAgents
    
    -- Get posts from all agents
    postIds = Array.concatMap (\aid ->
      case Map.lookup aid state.agentPosts of
        Nothing -> []
        Just ids -> ids
    ) allAgents
    
    -- Get posts
    posts = Array.mapMaybe (\pid -> Map.lookup pid state.posts) postIds
    
    -- Sort by creation time (newest first) and limit
    sorted = Array.reverse $ Array.sortBy (\a b -> compare a.createdAt b.createdAt) posts
  in
    Array.take limit sorted

-- | Get profile posts
getProfilePosts :: ProfileManagerState -> String -> Int -> Array AgentPost
getProfilePosts state agentId limit =
  case Map.lookup agentId state.agentPosts of
    Nothing -> []
    Just postIds ->
      let
        posts = Array.mapMaybe (\pid -> Map.lookup pid state.posts) postIds
        sorted = Array.reverse $ Array.sortBy (\a b -> compare a.createdAt b.createdAt) posts
      in
        Array.take limit sorted

