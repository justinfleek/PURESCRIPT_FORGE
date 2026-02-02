{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveGeneric #-}

-- | Session Sharing Service
-- | Migrated from opencode-dev/packages/enterprise/src/core/share.ts
module Render.Core.Share
  ( Info(..)
  , Data(..)
  , ShareError(..)
  , create
  , get
  , remove
  , sync
  , getData
  , syncOld
  ) where

import Prelude hiding (id)
import Control.Exception (Exception, throwIO)
import Control.Monad (forM_, when)
import Control.Concurrent.Async (mapConcurrently_)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Aeson (ToJSON(..), FromJSON(..), Value(..), object, (.=), (.:), (.:?), withObject)
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.KeyMap as KeyMap
import qualified Data.Aeson.Key as Key
import GHC.Generics (Generic)
import Data.Maybe (fromMaybe, catMaybes)
import Data.Time (getCurrentTime)
import Data.Time.Clock.POSIX (utcTimeToPOSIXSeconds)
import qualified Data.UUID as UUID
import qualified Data.UUID.V4 as UUID
import System.Environment (lookupEnv)
import Data.List (foldl')
import Data.Bits (xor, (.&.))
import Text.Printf (printf)
import Crypto.Random (getRandomBytes)
import qualified Data.ByteString as BS

import qualified Render.Core.Storage as Storage

data Info = Info
  { infoId        :: Text
  , infoSecret    :: Text
  , infoSessionID :: Text
  } deriving (Eq, Show, Generic)

instance ToJSON Info where
  toJSON Info {..} = object
    [ "id" .= infoId
    , "secret" .= infoSecret
    , "sessionID" .= infoSessionID
    ]

instance FromJSON Info where
  parseJSON = withObject "Info" $ \o -> Info
    <$> o .: "id"
    <*> o .: "secret"
    <*> o .: "sessionID"

data Data
  = SessionData Value
  | MessageData Value
  | PartData Value
  | SessionDiffData Value
  | ModelData Value
  deriving (Eq, Show, Generic)

instance ToJSON Data where
  toJSON = \case
    SessionData v -> object ["type" .= ("session" :: Text), "data" .= v]
    MessageData v -> object ["type" .= ("message" :: Text), "data" .= v]
    PartData v -> object ["type" .= ("part" :: Text), "data" .= v]
    SessionDiffData v -> object ["type" .= ("session_diff" :: Text), "data" .= v]
    ModelData v -> object ["type" .= ("model" :: Text), "data" .= v]

instance FromJSON Data where
  parseJSON = withObject "Data" $ \o -> do
    t <- o .: "type" :: Aeson.Parser Text
    d <- o .: "data"
    case t of
      "session" -> pure $ SessionData d
      "message" -> pure $ MessageData d
      "part" -> pure $ PartData d
      "session_diff" -> pure $ SessionDiffData d
      "model" -> pure $ ModelData d
      other -> fail $ "Unknown data type: " <> Text.unpack other

getField :: Text -> Value -> Text
getField field (Object o) = case KeyMap.lookup (Key.fromText field) o of
  Just (String t) -> t
  Just _ -> error $ "Field " <> Text.unpack field <> " is not a string"
  Nothing -> error $ "Missing field: " <> Text.unpack field
getField field _ = error $ "Expected object for field: " <> Text.unpack field

dataKey :: Data -> Text
dataKey = \case
  SessionData _ -> "session"
  MessageData v -> "message/" <> getField "id" v
  PartData v -> getField "messageID" v <> "/" <> getField "id" v
  SessionDiffData _ -> "session_diff"
  ModelData _ -> "model"

data Compaction = Compaction
  { compactionEvent :: Maybe Text
  , compactionData  :: [Data]
  } deriving (Eq, Show, Generic)

instance ToJSON Compaction where
  toJSON Compaction {..} = object
    [ "event" .= compactionEvent
    , "data" .= compactionData
    ]

instance FromJSON Compaction where
  parseJSON = withObject "Compaction" $ \o -> Compaction
    <$> o .:? "event"
    <*> o .: "data"

data ShareError
  = NotFound Text
  | InvalidSecret Text
  | AlreadyExists Text
  deriving (Eq, Show)

instance Exception ShareError

descending :: IO Text
descending = do
  now <- getCurrentTime
  let timestamp = utcTimeToPOSIXSeconds now
  let ms = round (timestamp * 1000) :: Integer
  let inverted = ms `xor` 0xFFFFFFFFFFFF
  let timeHex = Text.pack $ printf "%012x" (inverted .&. 0xFFFFFFFFFFFF :: Integer)
  randomPart <- randomBase62 14
  pure $ timeHex <> randomPart

randomBase62 :: Int -> IO Text
randomBase62 len = do
  bytes <- getRandomBytes len
  pure $ Text.pack [chars !! (fromIntegral b `mod` 62) | b <- BS.unpack bytes]
  where
    chars = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"

create :: Text -> IO Info
create sessionID = do
  nodeEnv <- lookupEnv "NODE_ENV"
  let isTest = nodeEnv == Just "test" || Text.isPrefixOf "test_" sessionID
  uuid <- UUID.nextRandom
  let prefix = if isTest then "test_" else ""
  let shareId = prefix <> Text.takeEnd 8 sessionID
  let info = Info shareId (UUID.toText uuid) sessionID
  existing <- get shareId
  case existing of
    Just _ -> throwIO $ AlreadyExists shareId
    Nothing -> do
      Storage.write ["share", shareId] info
      pure info

get :: Text -> IO (Maybe Info)
get shareId = Storage.read ["share", shareId]

remove :: Text -> Text -> IO ()
remove shareId secret = do
  share <- get shareId
  case share of
    Nothing -> throwIO $ NotFound shareId
    Just s -> do
      when (infoSecret s /= secret) $ throwIO $ InvalidSecret shareId
      Storage.remove ["share", shareId]
      items <- Storage.list (Just ["share_data", shareId]) Nothing Nothing Nothing
      forM_ items Storage.remove

sync :: Text -> Text -> [Data] -> IO ()
sync shareId secret items = do
  share <- get shareId
  case share of
    Nothing -> throwIO $ NotFound shareId
    Just s -> do
      when (infoSecret s /= secret) $ throwIO $ InvalidSecret shareId
      eventId <- descending
      Storage.write ["share_event", shareId, eventId] items

getData :: Text -> IO [Data]
getData shareId = do
  compaction <- fromMaybe (Compaction Nothing []) <$> Storage.read ["share_compaction", shareId]
  pending <- Storage.list (Just ["share_event", shareId]) Nothing Nothing (compactionEvent compaction)
  let reversed = reverse pending
  if null reversed
    then pure $ compactionData compaction
    else do
      events <- mapM (\k -> Storage.read k :: IO (Maybe [Data])) reversed
      let items = concat $ catMaybes events
      let merged = foldl' mergeItem (compactionData compaction) items
      let lastEvent = last (last reversed)
      Storage.write ["share_compaction", shareId] (Compaction (Just lastEvent) merged)
      pure merged

mergeItem :: [Data] -> Data -> [Data]
mergeItem arr item =
  let k = dataKey item
      (before, after) = span (\d -> dataKey d < k) arr
  in case after of
    (x:xs) | dataKey x == k -> before ++ [item] ++ xs
    _ -> before ++ [item] ++ after

syncOld :: Text -> Text -> [Data] -> IO ()
syncOld shareId secret items = do
  share <- get shareId
  case share of
    Nothing -> throwIO $ NotFound shareId
    Just s -> do
      when (infoSecret s /= secret) $ throwIO $ InvalidSecret shareId
      mapConcurrently_ (writeItem shareId) items

writeItem :: Text -> Data -> IO ()
writeItem shareId = \case
  SessionData v -> Storage.write ["share_data", shareId, "session"] v
  MessageData v -> Storage.write ["share_data", shareId, "message", getField "id" v] v
  PartData v -> Storage.write ["share_data", shareId, "part", getField "messageID" v, getField "id" v] v
  SessionDiffData v -> Storage.write ["share_data", shareId, "session_diff"] v
  ModelData v -> Storage.write ["share_data", shareId, "model"] v
