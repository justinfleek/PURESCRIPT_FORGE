-- | JSON-RPC Request/Response Decoding/Encoding FFI
module Bridge.FFI.Node.Handlers where

import Prelude
import Effect (Effect)
import Data.Either (Either)
import Data.Maybe (Maybe)
import Bridge.FFI.Node.FileContext (FileContextAddResponse, FileContextListResponse)
import Bridge.FFI.Node.Terminal (TerminalExecuteResponse)

-- | Session new request
type SessionNewRequest =
  { name :: Maybe String
  , parentId :: Maybe String
  , model :: Maybe String
  , provider :: Maybe String
  }

-- | Session new response
type SessionNewResponse =
  { sessionId :: String
  , success :: Boolean
  }

-- | File context add request
type FileContextAddRequest =
  { path :: String
  , sessionId :: Maybe String
  }

-- | File context list request
type FileContextListRequest =
  { sessionId :: Maybe String
  , filter :: Maybe String
  }

-- | Terminal execute request
type TerminalExecuteRequest =
  { command :: String
  , cwd :: Maybe String
  , sessionId :: Maybe String
  }

-- | Decode session.new request
foreign import decodeSessionNewRequest :: String -> Effect (Either String SessionNewRequest)

-- | Decode file.context.add request
foreign import decodeFileContextAddRequest :: String -> Effect (Either String FileContextAddRequest)

-- | Decode file.context.list request
foreign import decodeFileContextListRequest :: Maybe String -> Effect (Either String FileContextListRequest)

-- | Decode terminal.execute request
foreign import decodeTerminalExecuteRequest :: String -> Effect (Either String TerminalExecuteRequest)

-- | Encode session.new response
foreign import encodeSessionNewResponse :: SessionNewResponse -> Effect String

-- | Encode file.context.add response
foreign import encodeFileContextAddResponse :: FileContextAddResponse -> Effect String

-- | Encode file.context.list response
foreign import encodeFileContextListResponse :: FileContextListResponse -> Effect String

-- | Encode terminal.execute response
foreign import encodeTerminalExecuteResponse :: TerminalExecuteResponse -> Effect String

-- | Web search request
type WebSearchRequest =
  { query :: String
  , maxResults :: Maybe Int
  , sessionId :: Maybe String
  }

-- | Web search result
type WebSearchResult =
  { title :: String
  , url :: String
  , snippet :: String
  , relevance :: Number
  }

-- | Web search response
type WebSearchResponse =
  { success :: Boolean
  , results :: Array WebSearchResult
  , query :: String
  , totalResults :: Int
  }

-- | Decode web.search request
foreign import decodeWebSearchRequest :: String -> Effect (Either String WebSearchRequest)

-- | Encode web.search response
foreign import encodeWebSearchResponse :: WebSearchResponse -> Effect String

-- | Alert configuration request
type AlertConfigRequest =
  { diemWarningPercent :: Number
  , diemCriticalPercent :: Number
  , depletionWarningHours :: Number
  }

-- | Auth validate request
type AuthValidateRequest =
  { token :: String
  }

-- | Decode alerts.configure request
foreign import decodeAlertsConfigureRequest :: String -> Effect (Either String AlertConfigRequest)

-- | Generate authentication token
foreign import generateAuthToken :: Effect String

-- | Get authentication token expiry
foreign import getAuthTokenExpiry :: Effect String

-- | Decode auth.validate request
foreign import decodeAuthValidateRequest :: String -> Effect (Either String AuthValidateRequest)

-- | Validate authentication token
foreign import validateAuthToken :: String -> Effect Boolean

-- | Settings save request (full Settings type)
type SettingsSaveRequest =
  { alerts ::
      { warningPercent :: Number
      , criticalPercent :: Number
      , warningHours :: Number
      , soundEnabled :: Boolean
      }
  , appearance ::
      { theme :: String  -- "dark" | "light" | "system"
      }
  , keyboard ::
      { enabled :: Boolean
      , vimMode :: Boolean
      }
  , features ::
      { countdown :: Boolean
      , tokenCharts :: Boolean
      , proofPanel :: Boolean
      , timeline :: Boolean
      }
  , storage ::
      { retentionDays :: Int
      }
  }

-- | Settings save response
type SettingsSaveResponse =
  { success :: Boolean
  }

-- | Decode settings.save request
foreign import decodeSettingsSaveRequest :: String -> Effect (Either String SettingsSaveRequest)

-- | Encode settings.save response
foreign import encodeSettingsSaveResponse :: SettingsSaveResponse -> Effect String

-- | File read request
type FileReadRequest =
  { path :: String
  }

-- | File read response
type FileReadResponse =
  { success :: Boolean
  , content :: Maybe String
  , error :: Maybe String
  }

-- | Decode file.read request
foreign import decodeFileReadRequest :: String -> Effect (Either String FileReadRequest)

-- | Encode file.read response
foreign import encodeFileReadResponse :: FileReadResponse -> Effect String

-- | Lean apply tactic request
type LeanApplyTacticRequest =
  { file :: String
  , line :: Int
  , column :: Int
  , tactic :: String
  , goalIndex :: Maybe Int
  }

-- | Lean apply tactic response
type LeanApplyTacticResponse =
  { success :: Boolean
  , message :: Maybe String
  , goals :: Array { type_ :: String, context :: Array { name :: String, type_ :: String } }
  }

-- | Lean search theorems request
type LeanSearchTheoremsRequest =
  { query :: String
  , limit :: Maybe Int
  , file :: Maybe String
  }

-- | Lean search theorems response
type LeanSearchTheoremsResponse =
  { theorems :: Array { name :: String, statement :: String, file :: String, line :: Int, description :: Maybe String }
  , total :: Int
  }

-- | Decode lean.applyTactic request
foreign import decodeLeanApplyTacticRequest :: String -> Effect (Either String LeanApplyTacticRequest)

-- | Encode lean.applyTactic response
foreign import encodeLeanApplyTacticResponse :: LeanApplyTacticResponse -> Effect String

-- | Decode lean.searchTheorems request
foreign import decodeLeanSearchTheoremsRequest :: String -> Effect (Either String LeanSearchTheoremsRequest)

-- | Encode lean.searchTheorems response
foreign import encodeLeanSearchTheoremsResponse :: LeanSearchTheoremsResponse -> Effect String
