-- | Session Instructions
module Opencode.Session.Instruction where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Effect.Ref (Ref)
import Effect.Ref as Ref

-- | Instruction type
type Instruction =
  { id :: String
  , content :: String
  , priority :: Int
  , source :: String  -- "system", "user", "project"
  }

-- | Instruction storage (in production, would be part of SessionState)
instructionStorageRef :: Ref (Map.Map String (Array Instruction))
instructionStorageRef = unsafePerformEffect $ Ref.new Map.empty

-- | Get all active instructions for a session
getInstructions :: String -> Aff (Either String (Array Instruction))
getInstructions sessionId = do
  storage <- liftEffect $ Ref.read instructionStorageRef
  pure $ Right $ fromMaybe [] (Map.lookup sessionId storage)
  where
    fromMaybe :: forall a. a -> Maybe a -> a
    fromMaybe def = case _ of
      Nothing -> def
      Just x -> x

-- | Add an instruction
addInstruction :: String -> Instruction -> Aff (Either String Unit)
addInstruction sessionId instruction = do
  liftEffect $ Ref.modify_ (\storage ->
    let existing = fromMaybe [] (Map.lookup sessionId storage)
        updated = Array.snoc existing instruction
    in Map.insert sessionId updated storage
  ) instructionStorageRef
  pure $ Right unit
  where
    fromMaybe :: forall a. a -> Maybe a -> a
    fromMaybe def = case _ of
      Nothing -> def
      Just x -> x
