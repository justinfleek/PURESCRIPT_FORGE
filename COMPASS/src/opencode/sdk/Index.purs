-- | SDK - OpenCode SDK for PureScript
-- | Phase 4: SDK Migration
-- | This module provides the main SDK interface for creating clients and servers
module Opencode.SDK.Index
  ( module Opencode.SDK.Client
  , module Opencode.SDK.Server
  , createOpencode
  ) where

import Prelude

import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.SDK.Client as Client
import Opencode.SDK.Server as Server

-- | Re-export main SDK modules
export Opencode.SDK.Client
export Opencode.SDK.Server

-- | Create both client and server
-- | This matches the original SDK's createOpencode function
createOpencode :: Server.ServerOptions -> Aff (Either String Client.OpencodeSDK)
createOpencode options = do
  serverResult <- Server.createOpencodeServer options
  case serverResult of
    Left err -> pure $ Left err
    Right server -> do
      let client = Client.createOpencodeClient 
            { baseUrl: Just server.url
            , directory: Nothing
            , headers: Nothing
            , fetch: Nothing
            }
      pure $ Right { client, server }
