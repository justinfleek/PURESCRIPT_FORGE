-- | Test Data Generators
-- | Generators for test data
module Test.Bridge.Fixtures.TestData where

import Prelude
import Effect (Effect)
import Data.DateTime (DateTime)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Bridge.State.Store (BalanceState, SessionState, AlertLevel(..))

-- | Generate test balance state
generateBalanceState :: Effect BalanceState
generateBalanceState = do
  pure
    { venice:
        { diem: 1000.0
        , usd: 50.0
        , effective: 1050.0
        , lastUpdated: Nothing
        }
    , consumptionRate: 10.0
    , timeToDepletion: Just 100.0
    , todayUsed: 50.0
    , todayStartBalance: 1000.0
    , resetCountdown: Just 3600.0
    , alertLevel: Normal
    }

-- | Generate test session state
generateSessionState :: String -> Effect SessionState
generateSessionState sessionId = do
  now <- getCurrentDateTime
  pure
    { id: sessionId
    , promptTokens: 100
    , completionTokens: 200
    , totalTokens: 300
    , cost: 0.05
    , model: "claude-3-opus"
    , provider: "venice"
    , messageCount: 5
    , startedAt: now
    , updatedAt: now
    }

-- | Generate test JSON-RPC request
generateJsonRpcRequest :: String -> String -> String
generateJsonRpcRequest method params =
  """{"jsonrpc":"2.0","id":1,"method":\"""" <> method <> """","params":""" <> params <> """}"""

-- | Generate test JSON-RPC response
generateJsonRpcResponse :: String -> String
generateJsonRpcResponse result =
  """{"jsonrpc":"2.0","id":1,"result":""" <> result <> """}"""

-- | Generate test JSON-RPC error response
generateJsonRpcErrorResponse :: Int -> String -> Maybe String -> String
generateJsonRpcErrorResponse code message data_ =
  let dataStr = case data_ of
        Just d -> ""","data":""" <> d <> """}"""
        Nothing -> """}"""
  in """{"jsonrpc":"2.0","id":1,"error":{"code":""" <> show code <> ""","message":\"""" <> message <> "\"""" <> dataStr

-- | Generate test notification (no ID)
generateJsonRpcNotification :: String -> String -> String
generateJsonRpcNotification method params =
  """{"jsonrpc":"2.0","method":\"""" <> method <> """","params":""" <> params <> """}"""

foreign import getCurrentDateTime :: Effect DateTime
