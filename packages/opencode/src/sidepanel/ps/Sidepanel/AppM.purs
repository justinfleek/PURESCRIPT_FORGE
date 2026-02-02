-- | Application monad for OpenCode Sidepanel
-- | Based on spec 40-PURESCRIPT-ARCHITECTURE.md
module Sidepanel.AppM where

import Prelude
import Control.Monad.Reader (class MonadAsk, ReaderT, asks, runReaderT)
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)

-- | Application environment
type Env =
  { config :: Config
  , wsClient :: WebSocketClient
  }

-- | Configuration type
type Config =
  { veniceApiUrl :: String
  , opencodeApiUrl :: String
  , leanLspUrl :: Maybe String
  }

-- | WebSocket client (opaque type)
foreign import data WebSocketClient :: Type

-- | Application monad: ReaderT over Aff
newtype AppM a = AppM (ReaderT Env Aff a)

derive newtype instance functorAppM :: Functor AppM
derive newtype instance applyAppM :: Apply AppM
derive newtype instance applicativeAppM :: Applicative AppM
derive newtype instance bindAppM :: Bind AppM
derive newtype instance monadAppM :: Monad AppM
derive newtype instance monadEffectAppM :: MonadEffect AppM
derive newtype instance monadAffAppM :: MonadAff AppM
derive newtype instance monadAskAppM :: MonadAsk Env AppM

-- | Run AppM with environment
runAppM :: forall a. Env -> AppM a -> Aff a
runAppM env (AppM m) = runReaderT m env

-- | Capability: access WebSocket client
class Monad m <= MonadWebSocket m where
  getWsClient :: m WebSocketClient

instance monadWebSocketAppM :: MonadWebSocket AppM where
  getWsClient = AppM $ asks _.wsClient

-- | Capability: access config
class Monad m <= MonadConfig m where
  getConfig :: m Config

instance monadConfigAppM :: MonadConfig AppM where
  getConfig = AppM $ asks _.config
