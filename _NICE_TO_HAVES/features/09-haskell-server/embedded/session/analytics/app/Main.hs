-- | Bridge Analytics CLI
-- | Command-line interface for DuckDB analytics operations
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
module Main where

import Bridge.Analytics
import Bridge.Analytics.DuckDB
import Bridge.Analytics.Queries
import Data.Aeson (encode, decode, ToJSON, FromJSON)
import GHC.Generics (Generic)
import qualified Data.ByteString.Lazy as BL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import System.Environment (getArgs)
import System.IO (hPutStrLn, stderr)
import System.Exit (exitFailure)
import Data.Time.Format (parseTimeM, defaultTimeLocale, iso8601DateFormat)

-- | Query request data
data QueryRequest = QueryRequest
  { qrStart :: String
  , qrEnd :: String
  }
  deriving (Show, Generic)

instance ToJSON QueryRequest
instance FromJSON QueryRequest

-- | Parse UTCTime from ISO string
parseUTCTime :: String -> IO UTCTime
parseUTCTime s = do
  let formats = 
        [ "%Y-%m-%dT%H:%M:%S%QZ"
        , "%Y-%m-%dT%H:%M:%SZ"
        , "%Y-%m-%d %H:%M:%S"
        ]
  let parsed = foldl (\acc fmt -> case acc of
        Just _ -> acc
        Nothing -> parseTimeM True defaultTimeLocale fmt s
        ) Nothing formats
  case parsed of
    Just time -> return time
    Nothing -> error ("Failed to parse timestamp: " ++ s)

-- | Main entry point
main :: IO ()
main = do
  args <- getArgs
  case args of
    ["open", maybePath] -> do
      let path = if maybePath == ":memory:" then Nothing else Just maybePath
      handle <- openAnalytics path
      -- Output handle as JSON (simplified - just path for now)
      putStrLn (encode (maybePath :: String))
    
    ["load-sqlite", dbPath, sqlitePath] -> do
      handle <- openAnalytics (Just dbPath)
      loadFromSQLiteFFI handle sqlitePath
      putStrLn "loaded"
    
    ["query-token-usage", dbPath, input] -> do
      case decode (BL.fromStrict (TE.encodeUtf8 (T.pack input))) :: Maybe QueryRequest of
        Just req -> do
          handle <- openAnalytics (Just dbPath)
          start <- parseUTCTime (qrStart req)
          end <- parseUTCTime (qrEnd req)
          result <- queryTokenUsageByModelFFI handle (T.pack (qrStart req)) (T.pack (qrEnd req))
          putStrLn result
        Nothing -> do
          hPutStrLn stderr "Invalid query request"
          exitFailure
    
    ["query-cost-trends", dbPath, input] -> do
      case decode (BL.fromStrict (TE.encodeUtf8 (T.pack input))) :: Maybe QueryRequest of
        Just req -> do
          handle <- openAnalytics (Just dbPath)
          result <- queryCostTrendsFFI handle (T.pack (qrStart req)) (T.pack (qrEnd req))
          putStrLn result
        Nothing -> do
          hPutStrLn stderr "Invalid query request"
          exitFailure
    
    ["query-top-sessions", dbPath, limit] -> do
      handle <- openAnalytics (Just dbPath)
      result <- queryTopSessionsByCostFFI handle (read limit :: Int)
      putStrLn result
    
    ["query-model-performance", dbPath] -> do
      handle <- openAnalytics (Just dbPath)
      result <- queryModelPerformanceFFI handle
      putStrLn result
    
    ["query-balance-consumption", dbPath, input] -> do
      case decode (BL.fromStrict (TE.encodeUtf8 (T.pack input))) :: Maybe QueryRequest of
        Just req -> do
          handle <- openAnalytics (Just dbPath)
          result <- queryBalanceConsumptionFFI handle (T.pack (qrStart req)) (T.pack (qrEnd req))
          putStrLn result
        Nothing -> do
          hPutStrLn stderr "Invalid query request"
          exitFailure
    
    ["query-daily-summary", dbPath, input] -> do
      case decode (BL.fromStrict (TE.encodeUtf8 (T.pack input))) :: Maybe QueryRequest of
        Just req -> do
          handle <- openAnalytics (Just dbPath)
          result <- queryDailySummaryFFI handle (T.pack (qrStart req)) (T.pack (qrEnd req))
          putStrLn result
        Nothing -> do
          hPutStrLn stderr "Invalid query request"
          exitFailure
    
    _ -> do
      hPutStrLn stderr "Usage: bridge-analytics <command> [args...]"
      hPutStrLn stderr "Commands:"
      hPutStrLn stderr "  open <path|:memory:>"
      hPutStrLn stderr "  load-sqlite <dbPath> <sqlitePath>"
      hPutStrLn stderr "  query-token-usage <dbPath> <json>"
      hPutStrLn stderr "  query-cost-trends <dbPath> <json>"
      hPutStrLn stderr "  query-top-sessions <dbPath> <limit>"
      hPutStrLn stderr "  query-model-performance <dbPath>"
      hPutStrLn stderr "  query-balance-consumption <dbPath> <json>"
      hPutStrLn stderr "  query-daily-summary <dbPath> <json>"
      exitFailure
