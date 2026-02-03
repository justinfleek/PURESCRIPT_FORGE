{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- | Cloud Storage Adapter
-- | Supports S3 and R2 (Cloudflare) backends with lazy initialization
-- | Migrated from forge-dev/packages/enterprise/src/core/storage.ts
module Render.Core.Storage
  ( Adapter(..)
  , read
  , write
  , remove
  , list
  , update
  ) where

import Prelude hiding (read)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.ByteString.Lazy as BSL
import Data.Aeson (ToJSON, FromJSON)
import qualified Data.Aeson as Aeson
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import System.IO.Unsafe (unsafePerformIO)
import System.Environment (getEnv, lookupEnv)
import Data.Maybe (fromMaybe)
import Network.HTTP.Client (Manager, newManager, httpLbs, parseRequest, RequestBody(..), Response(..))
import Network.HTTP.Client.TLS (tlsManagerSettings)
import Network.HTTP.Types.Status (statusCode)
import qualified Network.HTTP.Client as HTTP
import Text.Regex.PCRE ((=~))
import qualified Data.ByteString.Char8 as BS8
import Network.AWS.Sign.V4 (signRequest)
import Network.AWS.Types (AccessKey(..), SecretKey(..), Region(..))

data Adapter = Adapter
  { adapterRead   :: Text -> IO (Maybe Text)
  , adapterWrite  :: Text -> Text -> IO ()
  , adapterRemove :: Text -> IO ()
  , adapterList   :: Maybe Text -> Maybe Int -> Maybe Text -> Maybe Text -> IO [Text]
  }

createAdapter :: Manager -> Text -> Text -> Text -> Text -> Text -> Adapter
createAdapter manager endpoint bucket region accessKeyId secretAccessKey =
  let base = endpoint <> "/" <> bucket
  in Adapter
    { adapterRead = \path -> do
        let url = Text.unpack $ base <> "/" <> path
        req <- parseRequest url
        response <- httpLbs req manager
        case statusCode (responseStatus response) of
          404 -> pure Nothing
          200 -> pure $ Just $ Text.decodeUtf8 $ BSL.toStrict $ responseBody response
          code -> error $ "Failed to read " <> Text.unpack path <> ": " <> show code

    , adapterWrite = \path value -> do
        let url = Text.unpack $ base <> "/" <> path
        initReq <- parseRequest url
        let req = initReq
              { HTTP.method = "PUT"
              , HTTP.requestBody = RequestBodyBS $ Text.encodeUtf8 value
              , HTTP.requestHeaders = [("Content-Type", "application/json")]
              }
        response <- httpLbs req manager
        case statusCode (responseStatus response) of
          200 -> pure ()
          201 -> pure ()
          code -> error $ "Failed to write " <> Text.unpack path <> ": " <> show code

    , adapterRemove = \path -> do
        let url = Text.unpack $ base <> "/" <> path
        initReq <- parseRequest url
        let req = initReq { HTTP.method = "DELETE" }
        response <- httpLbs req manager
        case statusCode (responseStatus response) of
          200 -> pure ()
          204 -> pure ()
          code -> error $ "Failed to remove " <> Text.unpack path <> ": " <> show code

    , adapterList = \prefix limit after before -> do
        let pfx = fromMaybe "" prefix
        let params = [("list-type", "2"), ("prefix", Text.unpack pfx)]
              ++ maybe [] (\l -> [("max-keys", show l)]) limit
              ++ maybe [] (\a -> [("start-after", Text.unpack pfx <> Text.unpack a <> ".json")]) after
        let queryString = concatMap (\(k,v) -> k <> "=" <> v <> "&") params
        let url = Text.unpack base <> "?" <> init queryString
        req <- parseRequest url
        response <- httpLbs req manager
        case statusCode (responseStatus response) of
          200 -> do
            let xml = Text.decodeUtf8 $ BSL.toStrict $ responseBody response
            let keys = extractKeys xml
            case before of
              Nothing -> pure keys
              Just b -> do
                let beforePath = pfx <> b <> ".json"
                pure $ filter (< beforePath) keys
          code -> error $ "Failed to list " <> Text.unpack pfx <> ": " <> show code
    }

extractKeys :: Text -> [Text]
extractKeys xml =
  let pattern = "<Key>([^<]+)</Key>" :: String
      matches = Text.unpack xml =~ pattern :: [[String]]
  in [Text.pack (m !! 1) | m <- matches, length m > 1]

s3 :: IO Adapter
s3 = do
  bucket <- getEnv "OPENCODE_STORAGE_BUCKET"
  region <- fromMaybe "us-east-1" <$> lookupEnv "OPENCODE_STORAGE_REGION"
  accessKeyId <- getEnv "OPENCODE_STORAGE_ACCESS_KEY_ID"
  secretAccessKey <- getEnv "OPENCODE_STORAGE_SECRET_ACCESS_KEY"
  manager <- newManager tlsManagerSettings
  let endpoint = "https://s3." <> Text.pack region <> ".amazonaws.com"
  pure $ createAdapter manager endpoint (Text.pack bucket) (Text.pack region) (Text.pack accessKeyId) (Text.pack secretAccessKey)

r2 :: IO Adapter
r2 = do
  accountId <- getEnv "OPENCODE_STORAGE_ACCOUNT_ID"
  accessKeyId <- getEnv "OPENCODE_STORAGE_ACCESS_KEY_ID"
  secretAccessKey <- getEnv "OPENCODE_STORAGE_SECRET_ACCESS_KEY"
  bucket <- getEnv "OPENCODE_STORAGE_BUCKET"
  manager <- newManager tlsManagerSettings
  let endpoint = "https://" <> Text.pack accountId <> ".r2.cloudflarestorage.com"
  pure $ createAdapter manager endpoint (Text.pack bucket) "auto" (Text.pack accessKeyId) (Text.pack secretAccessKey)

{-# NOINLINE adapterRef #-}
adapterRef :: IORef (Maybe Adapter)
adapterRef = unsafePerformIO $ newIORef Nothing

adapter :: IO Adapter
adapter = do
  cached <- readIORef adapterRef
  case cached of
    Just a -> pure a
    Nothing -> do
      adapterType <- lookupEnv "OPENCODE_STORAGE_ADAPTER"
      a <- case adapterType of
        Just "r2" -> r2
        Just "s3" -> s3
        _ -> error "No storage adapter configured"
      writeIORef adapterRef (Just a)
      pure a

resolve :: [Text] -> Text
resolve key = Text.intercalate "/" key <> ".json"

read :: FromJSON a => [Text] -> IO (Maybe a)
read key = do
  a <- adapter
  result <- adapterRead a (resolve key)
  case result of
    Nothing -> pure Nothing
    Just txt -> pure $ Aeson.decode $ BSL.fromStrict $ Text.encodeUtf8 txt

write :: ToJSON a => [Text] -> a -> IO ()
write key value = do
  a <- adapter
  let json = Text.decodeUtf8 $ BSL.toStrict $ Aeson.encode value
  adapterWrite a (resolve key) json

remove :: [Text] -> IO ()
remove key = do
  a <- adapter
  adapterRemove a (resolve key)

list :: Maybe [Text] -> Maybe Int -> Maybe Text -> Maybe Text -> IO [[Text]]
list prefix limit after before = do
  a <- adapter
  let p = case prefix of
        Nothing -> ""
        Just ps -> Text.intercalate "/" ps <> (if null ps then "" else "/")
  result <- adapterList a (Just p) limit after before
  pure $ map (\x -> Text.splitOn "/" (fromMaybe x (Text.stripSuffix ".json" x))) result

update :: (FromJSON a, ToJSON a) => [Text] -> (a -> a) -> IO a
update key fn = do
  val <- read key
  case val of
    Nothing -> error "Not found"
    Just v -> do
      let updated = fn v
      write key updated
      pure updated
