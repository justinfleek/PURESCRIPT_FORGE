-- | Logging utilities
module Opencode.Util.Log where

import Prelude
import Effect (Effect)
import Effect.Console as Console
import Effect.Ref as Effect
import Data.String as String

-- | Log level
data LogLevel
  = Debug
  | Info
  | Warn
  | Error

derive instance eqLogLevel :: Eq LogLevel

instance ordLogLevel :: Ord LogLevel where
  compare Debug Debug = EQ
  compare Debug _ = LT
  compare Info Info = EQ
  compare Info Debug = GT
  compare Info _ = LT
  compare Warn Warn = EQ
  compare Warn Error = LT
  compare Warn _ = GT
  compare Error Error = EQ
  compare Error _ = GT

-- | Logger configuration
type LoggerConfig =
  { service :: String
  , level :: LogLevel
  }

-- | Logger instance
type Logger =
  { debug :: String -> Effect Unit
  , info :: String -> Effect Unit
  , warn :: String -> Effect Unit
  , error :: String -> Effect Unit
  }

-- | Global log level (default: Info)
logLevelRef :: Effect.Ref LogLevel
logLevelRef = unsafePerformEffect $ Effect.Ref.new Info
  where
    foreign import unsafePerformEffect :: forall a. Effect a -> a

-- | Check if should log at given level
shouldLog :: LogLevel -> LogLevel -> Boolean
shouldLog messageLevel configLevel = messageLevel >= configLevel

-- | Format log message
formatMessage :: String -> LogLevel -> String -> String
formatMessage service level message =
  let levelStr = case level of
        Debug -> "DEBUG"
        Info -> "INFO "
        Warn -> "WARN "
        Error -> "ERROR"
  in "[" <> levelStr <> "] " <> service <> ": " <> message

-- | Create a logger
create :: LoggerConfig -> Logger
create config =
  { debug: \msg -> do
      currentLevel <- Effect.Ref.read logLevelRef
      if shouldLog Debug currentLevel
        then Console.log (formatMessage config.service Debug msg)
        else pure unit
  , info: \msg -> do
      currentLevel <- Effect.Ref.read logLevelRef
      if shouldLog Info currentLevel
        then Console.log (formatMessage config.service Info msg)
        else pure unit
  , warn: \msg -> do
      currentLevel <- Effect.Ref.read logLevelRef
      if shouldLog Warn currentLevel
        then Console.warn (formatMessage config.service Warn msg)
        else pure unit
  , error: \msg -> do
      currentLevel <- Effect.Ref.read logLevelRef
      if shouldLog Error currentLevel
        then Console.error (formatMessage config.service Error msg)
        else pure unit
  }
