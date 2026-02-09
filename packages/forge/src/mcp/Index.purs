{-|
Module      : Forge.MCP.Index
Description : Model Context Protocol server management
= MCP Module

Manages MCP (Model Context Protocol) server connections for extended
tool capabilities.

== Overview

MCP allows connecting external tool servers that provide additional
capabilities beyond the built-in tools.

== MCP Server Lifecycle

@
  1. Discovery: Find configured MCP servers
  2. Connection: Establish stdio/sse transport
  3. Capabilities: Query tools and resources
  4. Execution: Call tools, read resources
  5. Shutdown: Graceful disconnection
@

== Supported Transports

| Transport | Description                     |
|-----------|---------------------------------|
| stdio     | Process stdin/stdout            |
| sse       | Server-Sent Events over HTTP    |

-}
module Forge.MCP.Index
  ( -- * Types
    MCPServer(..)
  , MCPServerConfig(..)
  , MCPTool(..)
  , MCPResource(..)
  , MCPTransport(..)
  , MCPState
    -- * Server Management
  , init
  , listServers
  , getServer
  , connect
  , disconnect
    -- * Tool Execution
  , callTool
  , listTools
    -- * Resource Access
  , readResource
  , listResources
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Argonaut (Json, encodeJson, decodeJson)
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | MCP transport type
data MCPTransport
  = StdioTransport
  | SSETransport String  -- URL for SSE

derive instance eqMCPTransport :: Eq MCPTransport

instance showMCPTransport :: Show MCPTransport where
  show StdioTransport = "stdio"
  show (SSETransport url) = "sse:" <> url

-- | MCP server configuration
type MCPServerConfig =
  { id :: String
  , name :: String
  , command :: Maybe String      -- For stdio transport
  , args :: Array String
  , url :: Maybe String          -- For sse transport
  , env :: Maybe (Array { key :: String, value :: String })
  , timeout :: Int
  }

-- | MCP server instance
type MCPServer =
  { id :: String
  , name :: String
  , transport :: MCPTransport
  , tools :: Array MCPTool
  , resources :: Array MCPResource
  , connected :: Boolean
  }

-- | MCP tool definition
type MCPTool =
  { name :: String
  , description :: String
  , inputSchema :: Json
  }

-- | MCP resource definition
type MCPResource =
  { uri :: String
  , name :: String
  , description :: Maybe String
  , mimeType :: Maybe String
  }

-- | MCP state (opaque type)
type MCPState =
  { servers :: Array MCPServer
  , initialized :: Boolean
  }

-- | Tool call result
type ToolCallResult =
  { content :: Array ContentBlock
  , isError :: Boolean
  }

type ContentBlock =
  { blockType :: String  -- "text", "image", "resource"
  , text :: Maybe String
  , data :: Maybe String
  , mimeType :: Maybe String
  }

-- ============================================================================
-- SERVER MANAGEMENT
-- ============================================================================

-- | Initialize MCP system
init :: Aff (Either String MCPState)
init = do
  -- Load MCP server configurations from config
  configs <- loadMCPConfigsFFI
  case configs of
    Left err -> pure $ Left err
    Right serverConfigs -> do
      -- Create initial state with configured servers (not yet connected)
      let servers = map mkServerFromConfig serverConfigs
      pure $ Right
        { servers
        , initialized: true
        }

-- | Create server instance from config
mkServerFromConfig :: MCPServerConfig -> MCPServer
mkServerFromConfig config =
  { id: config.id
  , name: config.name
  , transport: case config.url of
      Just url -> SSETransport url
      Nothing -> StdioTransport
  , tools: []
  , resources: []
  , connected: false
  }

-- | FFI for loading MCP configs
foreign import loadMCPConfigsFFI :: Aff (Either String (Array MCPServerConfig))

-- | List all configured MCP servers
listServers :: MCPState -> Array MCPServer
listServers state = state.servers

-- | Get server by ID
getServer :: String -> MCPState -> Maybe MCPServer
getServer serverId state = 
  Array.find (\s -> s.id == serverId) state.servers

-- | Connect to an MCP server
connect :: String -> MCPState -> Aff (Either String MCPState)
connect serverId state = do
  case getServer serverId state of
    Nothing -> pure $ Left $ "Server not found: " <> serverId
    Just server -> do
      if server.connected then
        pure $ Right state
      else do
        -- Connect to server via transport
        result <- connectServerFFI server
        case result of
          Left err -> pure $ Left err
          Right connectedServer -> do
            -- Update state with connected server
            let servers' = map 
                  (\s -> if s.id == serverId then connectedServer else s)
                  state.servers
            pure $ Right $ state { servers = servers' }

-- | FFI for connecting to MCP server
foreign import connectServerFFI :: MCPServer -> Aff (Either String MCPServer)

-- | Disconnect from an MCP server
disconnect :: String -> MCPState -> Aff (Either String MCPState)
disconnect serverId state = do
  case getServer serverId state of
    Nothing -> pure $ Left $ "Server not found: " <> serverId
    Just server -> do
      if not server.connected then
        pure $ Right state
      else do
        -- Disconnect from server
        result <- disconnectServerFFI server
        case result of
          Left err -> pure $ Left err
          Right _ -> do
            -- Update state with disconnected server
            let servers' = map 
                  (\s -> if s.id == serverId 
                         then s { connected = false, tools = [], resources = [] }
                         else s)
                  state.servers
            pure $ Right $ state { servers = servers' }

-- | FFI for disconnecting from MCP server
foreign import disconnectServerFFI :: MCPServer -> Aff (Either String Unit)

-- ============================================================================
-- TOOL EXECUTION
-- ============================================================================

-- | List tools from all connected servers
listTools :: MCPState -> Array { serverId :: String, tool :: MCPTool }
listTools state =
  Array.concatMap 
    (\server -> 
      if server.connected 
      then map (\t -> { serverId: server.id, tool: t }) server.tools
      else [])
    state.servers

-- | Call an MCP tool
callTool :: String -> String -> Json -> MCPState -> Aff (Either String ToolCallResult)
callTool serverId toolName arguments state = do
  case getServer serverId state of
    Nothing -> pure $ Left $ "Server not found: " <> serverId
    Just server -> do
      if not server.connected then
        pure $ Left $ "Server not connected: " <> serverId
      else do
        -- Find tool
        case Array.find (\t -> t.name == toolName) server.tools of
          Nothing -> pure $ Left $ "Tool not found: " <> toolName
          Just tool -> callToolFFI server toolName arguments

-- | FFI for calling MCP tool
foreign import callToolFFI :: MCPServer -> String -> Json -> Aff (Either String ToolCallResult)

-- ============================================================================
-- RESOURCE ACCESS
-- ============================================================================

-- | List resources from all connected servers
listResources :: MCPState -> Array { serverId :: String, resource :: MCPResource }
listResources state =
  Array.concatMap 
    (\server -> 
      if server.connected 
      then map (\r -> { serverId: server.id, resource: r }) server.resources
      else [])
    state.servers

-- | Read an MCP resource
readResource :: String -> String -> MCPState -> Aff (Either String String)
readResource serverId uri state = do
  case getServer serverId state of
    Nothing -> pure $ Left $ "Server not found: " <> serverId
    Just server -> do
      if not server.connected then
        pure $ Left $ "Server not connected: " <> serverId
      else readResourceFFI server uri

-- | FFI for reading MCP resource
foreign import readResourceFFI :: MCPServer -> String -> Aff (Either String String)
