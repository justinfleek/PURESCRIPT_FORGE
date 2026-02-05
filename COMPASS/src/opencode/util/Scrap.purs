-- | Scrap utilities (temporary/scratch data)
module Opencode.Util.Scrap where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))

-- | In-memory scrap storage
scrapStorageRef :: Ref (Map.Map String String)
scrapStorageRef = unsafePerformEffect $ Ref.new Map.empty
  where
    foreign import unsafePerformEffect :: forall a. Effect a -> a

-- | Save scrap data
save :: String -> String -> Aff (Either String Unit)
save key data_ = do
  liftEffect $ Ref.modify_ (\storage -> Map.insert key data_ storage) scrapStorageRef
  pure $ Right unit

-- | Load scrap data
load :: String -> Aff (Either String String)
load key = do
  storage <- liftEffect $ Ref.read scrapStorageRef
  case Map.lookup key storage of
    Nothing -> pure $ Left ("Scrap key not found: " <> key)
    Just value -> pure $ Right value

-- | Clear scrap data
clear :: String -> Aff (Either String Unit)
clear key = do
  liftEffect $ Ref.modify_ (\storage -> Map.delete key storage) scrapStorageRef
  pure $ Right unit

import Effect (Effect)
