-- | NEXUS Agent Handlers - JSON-RPC handlers for NEXUS agent operations
module Bridge.NEXUS.Handlers where

import Prelude
import Effect (Effect)
import Bridge.WebSocket.Handlers.Types (JsonRpcRequest, JsonRpcResponse, successResponse, errorResponse)
import Data.Maybe (Maybe(..))

-- | FFI declarations (top-level)
foreign import nexusAgentLaunchImpl :: JsonRpcRequest -> Effect JsonRpcResponse
foreign import nexusAgentStatusImpl :: JsonRpcRequest -> Effect JsonRpcResponse
foreign import nexusAgentProfileImpl :: JsonRpcRequest -> Effect JsonRpcResponse
foreign import nexusAttestationCreateImpl :: JsonRpcRequest -> Effect JsonRpcResponse

-- | Launch NEXUS agent
nexusAgentLaunch :: JsonRpcRequest -> Effect JsonRpcResponse
nexusAgentLaunch = nexusAgentLaunchImpl

-- | Get NEXUS agent status
nexusAgentStatus :: JsonRpcRequest -> Effect JsonRpcResponse
nexusAgentStatus = nexusAgentStatusImpl

-- | Get NEXUS agent profile
nexusAgentProfile :: JsonRpcRequest -> Effect JsonRpcResponse
nexusAgentProfile = nexusAgentProfileImpl

-- | Create attestation
nexusAttestationCreate :: JsonRpcRequest -> Effect JsonRpcResponse
nexusAttestationCreate = nexusAttestationCreateImpl
