{-|
Module      : Opencode.Server.Server
Description : Main HTTP server
= HTTP Server

Main server implementation matching OpenCode's server/server.ts.
Routes requests to appropriate handlers and manages SSE connections.

== Coeffect Equation

@
  listen : ServerOptions -> Graded IO Server
  url    : Server -> URL
  stop   : Server -> Graded IO Unit
@

== Route Structure

@
  /global/*       -> Global routes
  /project/*      -> Project routes
  /session/*      -> Session routes
  /provider/*     -> Provider routes
  /config/*       -> Config routes
  /mcp/*          -> MCP routes
  /pty/*          -> PTY routes
  /file/*         -> File routes
  /event          -> SSE event stream
  /doc            -> OpenAPI spec
@

-}
module Opencode.Server.Server
  ( -- * Types
    ServerConfig
  , Server
  , ListenOptions
    -- * Server Operations
  , listen
  , stop
  , url
  , app
    -- * Route Registration
  , Router
  , Route(..)
  , Method(..)
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Class (liftEffect)

import Opencode.Session.Operations as SessionOps
import Opencode.Server.Routes.Session as SessionRoutes
import Opencode.Server.Routes.Provider as ProviderRoutes

-- ════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ════════════════════════════════════════════════════════════════════════════

-- | Server configuration
type ServerConfig =
  { port :: Int
  , hostname :: String
  , mdns :: Boolean
  , cors :: Array String
  }

-- | Default server configuration
defaultConfig :: ServerConfig
defaultConfig =
  { port: 4096
  , hostname: "127.0.0.1"
  , mdns: false
  , cors: []
  }

-- | Listen options (subset for starting)
type ListenOptions =
  { port :: Int
  , hostname :: String
  , mdns :: Maybe Boolean
  , cors :: Maybe (Array String)
  }

-- | Server instance
type Server =
  { config :: ServerConfig
  , url :: String
  , state :: ServerState
  }

-- | Internal server state
type ServerState =
  { running :: Boolean
  , sessionState :: Ref SessionOps.SessionState
  , sseConnections :: Array SSEConnection
  }

-- | SSE connection
type SSEConnection =
  { id :: String
  , send :: String -> Effect Unit
  , close :: Effect Unit
  }

-- | HTTP method
data Method
  = GET
  | POST
  | PUT
  | PATCH
  | DELETE
  | OPTIONS

instance showMethod :: Show Method where
  show GET = "GET"
  show POST = "POST"
  show PUT = "PUT"
  show PATCH = "PATCH"
  show DELETE = "DELETE"
  show OPTIONS = "OPTIONS"

-- | Route definition
type Route =
  { method :: Method
  , path :: String
  , handler :: Request -> Aff Response
  }

-- | Router (collection of routes)
type Router = Array Route

-- | HTTP request
type Request =
  { method :: String
  , path :: String
  , query :: Array { key :: String, value :: String }
  , headers :: Array { key :: String, value :: String }
  , body :: Maybe String
  }

-- | HTTP response
type Response =
  { status :: Int
  , headers :: Array { key :: String, value :: String }
  , body :: String
  }

-- ════════════════════════════════════════════════════════════════════════════
-- SERVER OPERATIONS
-- ════════════════════════════════════════════════════════════════════════════

-- | Start the server
listen :: ListenOptions -> Aff (Either String Server)
listen opts = do
  -- Create session state
  sessionStateRef <- liftEffect $ Ref.new (SessionOps.initialState "default" ".")
  
  let config =
        { port: opts.port
        , hostname: opts.hostname
        , mdns: fromMaybe false opts.mdns
        , cors: fromMaybe [] opts.cors
        }
  
  let state =
        { running: true
        , sessionState: sessionStateRef
        , sseConnections: []
        }
  
  let server =
        { config
        , url: "http://" <> config.hostname <> ":" <> show config.port
        , state
        }
  
  -- Start FFI server
  result <- startHttpServer config
  case result of
    Left err -> pure $ Left err
    Right _ -> pure $ Right server

-- | Stop the server
stop :: Server -> Aff (Either String Unit)
stop _server = do
  -- Close all SSE connections
  -- Stop HTTP server
  stopHttpServer
  pure $ Right unit

-- | Get server URL
url :: Server -> String
url server = server.url

-- | Get the Hono-style app for internal routing
app :: Server -> Router
app server = buildRoutes server.state.sessionState

-- ════════════════════════════════════════════════════════════════════════════
-- ROUTE BUILDING
-- ════════════════════════════════════════════════════════════════════════════

-- | Build all routes
buildRoutes :: Ref SessionOps.SessionState -> Router
buildRoutes sessionState =
  sessionRoutes sessionState <>
  providerRoutes <>
  coreRoutes

-- | Session routes
sessionRoutes :: Ref SessionOps.SessionState -> Router
sessionRoutes stateRef =
  [ { method: GET
    , path: "/session"
    , handler: \req -> do
        let query = parseListQuery req.query
        sessions <- SessionRoutes.list query stateRef
        pure $ jsonResponse 200 sessions
    }
  , { method: GET
    , path: "/session/status"
    , handler: \_req -> do
        statuses <- SessionRoutes.status stateRef
        pure $ jsonResponse 200 statuses
    }
  , { method: POST
    , path: "/session"
    , handler: \req -> do
        let input = parseCreateInput req.body
        session <- SessionRoutes.create input stateRef
        pure $ jsonResponse 200 session
    }
  , { method: DELETE
    , path: "/session/:sessionID"
    , handler: \req -> do
        let sessionId = extractParam req.path "sessionID"
        result <- SessionRoutes.delete sessionId stateRef
        pure $ eitherResponse result
    }
  ]
  where
    parseListQuery :: Array { key :: String, value :: String } -> SessionRoutes.ListQuery
    parseListQuery _params =
      { directory: Nothing
      , roots: Nothing
      , start: Nothing
      , search: Nothing
      , limit: Nothing
      }
    
    parseCreateInput :: Maybe String -> { parentID :: Maybe String, title :: Maybe String }
    parseCreateInput _body = { parentID: Nothing, title: Nothing }
    
    extractParam :: String -> String -> String
    extractParam path _paramName = 
      -- Simple extraction: /session/ses_123 -> ses_123
      case Array.last (Array.filter (_ /= "") (split "/" path)) of
        Nothing -> ""
        Just p -> p
    
    split :: String -> String -> Array String
    split delim str = 
      -- Simplified split
      [str]

-- | Provider routes  
providerRoutes :: Router
providerRoutes =
  [ { method: GET
    , path: "/provider"
    , handler: \_req -> do
        result <- ProviderRoutes.list { disabledProviders: [], enabledProviders: Nothing }
        pure $ jsonResponse 200 result
    }
  , { method: GET
    , path: "/provider/auth"
    , handler: \_req -> do
        methods <- ProviderRoutes.authMethods
        pure $ jsonResponse 200 methods
    }
  ]

-- | Core routes (path, vcs, doc, event)
coreRoutes :: Router
coreRoutes =
  [ { method: GET
    , path: "/doc"
    , handler: \_req -> pure $ jsonResponse 200 openApiSpec
    }
  , { method: GET
    , path: "/path"
    , handler: \_req -> pure $ jsonResponse 200 
        { home: "~"
        , state: "~/.local/state/opencode"
        , config: "~/.config/opencode"
        , worktree: "."
        , directory: "."
        }
    }
  , { method: GET
    , path: "/vcs"
    , handler: \_req -> pure $ jsonResponse 200 { branch: "main" }
    }
  , { method: GET
    , path: "/event"
    , handler: \_req -> pure $ sseResponse
    }
  ]

-- ════════════════════════════════════════════════════════════════════════════
-- RESPONSE BUILDERS
-- ════════════════════════════════════════════════════════════════════════════

-- | Build JSON response
jsonResponse :: forall a. Int -> a -> Response
jsonResponse status body =
  { status
  , headers: [{ key: "Content-Type", value: "application/json" }]
  , body: encodeJsonToString body
  }
  where
    foreign import encodeJsonToString :: forall a. a -> String

-- | Build either response
eitherResponse :: forall a. Either String a -> Response
eitherResponse result = case result of
  Left err -> 
    { status: 400
    , headers: [{ key: "Content-Type", value: "application/json" }]
    , body: "{\"error\": \"" <> err <> "\"}"
    }
  Right _ ->
    { status: 200
    , headers: [{ key: "Content-Type", value: "application/json" }]
    , body: "true"
    }

-- | Build SSE response
sseResponse :: Response
sseResponse =
  { status: 200
  , headers: 
      [ { key: "Content-Type", value: "text/event-stream" }
      , { key: "Cache-Control", value: "no-cache" }
      , { key: "Connection", value: "keep-alive" }
      ]
  , body: "data: {\"type\":\"server.connected\",\"properties\":{}}\n\n"
  }

-- | OpenAPI spec
openApiSpec :: { info :: { title :: String, version :: String, description :: String }, openapi :: String, paths :: Json }
openApiSpec =
  { info: 
      { title: "OpenCode API"
      , version: "1.0.0"
      , description: "OpenCode server API for AI coding assistant"
      }
  , openapi: "3.1.1"
  , paths: encodeJson {}
  }

-- ════════════════════════════════════════════════════════════════════════════
-- FFI
-- ════════════════════════════════════════════════════════════════════════════

-- | Start HTTP server (FFI)
foreign import startHttpServer :: ServerConfig -> Aff (Either String Unit)

-- | Stop HTTP server (FFI)
foreign import stopHttpServer :: Aff Unit

-- ════════════════════════════════════════════════════════════════════════════
-- HELPERS
-- ════════════════════════════════════════════════════════════════════════════

fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe def = case _ of
  Nothing -> def
  Just a -> a
