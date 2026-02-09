-- | Nexus Database Layer - PureScript PostgreSQL Bindings
-- | PureScript interface to PostgreSQL database operations
module Nexus.Database.Postgres where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff, makeAff, nonCanceler)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Argonaut (Json, jsonParser, decodeJson, class DecodeJson)

-- | Opaque PostgreSQL pool handle type
foreign import data PostgresPool :: Type

-- | Initialize PostgreSQL connection pool from DATABASE_URL
-- | Reads DATABASE_URL from environment (set by Fly.io)
foreign import initPostgresPool :: Effect PostgresPool

-- | Initialize PostgreSQL connection pool from explicit URL
foreign import initPostgresPoolFromUrl :: String -> Effect PostgresPool

-- | Close PostgreSQL connection pool
foreign import closePostgresPool :: PostgresPool -> Effect Unit

-- | Execute query and return results (JSON)
foreign import executeQueryJson_ :: PostgresPool -> String -> Array String -> Effect (Aff String)

executeQueryJson :: PostgresPool -> String -> Array String -> Aff String
executeQueryJson pool query params = makeAff \callback -> do
  affResult <- executeQueryJson_ pool query params
  callback affResult
  pure nonCanceler

-- | Query semantic cells (direct PostgreSQL query)
foreign import querySemanticCells_ :: PostgresPool -> Maybe String -> Maybe String -> Maybe String -> Maybe Int -> Effect (Aff String)

querySemanticCells :: PostgresPool -> Maybe String -> Maybe String -> Maybe String -> Maybe Int -> Aff (Either String Json)
querySemanticCells pool mLevel mDomain mBasin mLimit = do
  result <- makeAff \callback -> do
    affResult <- querySemanticCells_ pool mLevel mDomain mBasin mLimit
    callback affResult
    pure nonCanceler
  case jsonParser result of
    Left err -> pure $ Left err
    Right json -> pure $ Right json

-- | Save semantic cell (direct PostgreSQL query)
foreign import saveSemanticCell_ :: PostgresPool -> String -> Effect (Aff String)

saveSemanticCell :: PostgresPool -> String -> Aff (Either String Unit)
saveSemanticCell pool cellJson = do
  result <- makeAff \callback -> do
    affResult <- saveSemanticCell_ pool cellJson
    callback affResult
    pure nonCanceler
  case jsonParser result of
    Left err -> pure $ Left err
    Right _ -> pure $ Right unit

-- | Load semantic cell by ID (direct PostgreSQL query)
foreign import loadSemanticCell_ :: PostgresPool -> String -> Effect (Aff String)

loadSemanticCell :: PostgresPool -> String -> Aff (Either String (Maybe Json))
loadSemanticCell pool cellId = do
  result <- makeAff \callback -> do
    affResult <- loadSemanticCell_ pool cellId
    callback affResult
    pure nonCanceler
  case jsonParser result of
    Left err -> pure $ Left err
    Right json -> case json `decodeJson` of
      Left _ -> pure $ Right Nothing
      Right null -> pure $ Right Nothing
      Right cell -> pure $ Right (Just cell)
