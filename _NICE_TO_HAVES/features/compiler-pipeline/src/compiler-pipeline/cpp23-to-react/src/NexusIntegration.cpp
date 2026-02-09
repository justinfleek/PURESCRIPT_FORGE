// Nexus Integration: Agent Launch Button Generator Implementation
#include "NexusIntegration.h"
#include "RadixBinder.h"
#include <sstream>
#include <algorithm>

namespace nexus_integration {

// Generate React component with agent launch button
std::string generate_agent_launch_button(
    const AgentLaunchTask& task,
    const std::string& component_name
) {
    std::ostringstream oss;
    
    oss << "import * as React from 'react';\n";
    oss << "import * as Button from '@radix-ui/react-button';\n";
    oss << "import * as Dialog from '@radix-ui/react-dialog';\n";
    oss << "import * as Progress from '@radix-ui/react-progress';\n";
    oss << "import * as Avatar from '@radix-ui/react-avatar';\n";
    oss << "import { useWebSocket } from '@/hooks/useWebSocket';\n";
    oss << "import { useAttestation } from '@/hooks/useAttestation';\n";
    oss << "import { cn } from '@/lib/utils';\n\n";
    
    oss << "export interface " << component_name << "Props {\n";
    oss << "  taskId?: string;\n";
    oss << "  taskDescription: string;\n";
    oss << "  agentType: 'web_search' | 'content_extraction' | 'network_formation' | 'research';\n";
    oss << "  config?: Record<string, string>;\n";
    oss << "  agentId?: string;\n";
    oss << "  agentDisplayName?: string;\n";
    oss << "  agentAvatarUrl?: string;\n";
    oss << "  onComplete?: (result: { agentId: string; success: boolean }) => void;\n";
    oss << "  className?: string;\n";
    oss << "}\n\n";
    
    oss << "export const " << component_name << ": React.FC<" << component_name << "Props> = (props) => {\n";
    oss << "  const { taskDescription, agentType, config = {}, agentId: propAgentId, agentDisplayName, agentAvatarUrl, onComplete, className } = props;\n";
    oss << "  const taskId = props.taskId || `task-${Date.now()}`;\n\n";
    
    oss << "  // Agent profile state\n";
    oss << "  const [agentId, setAgentId] = React.useState<string | null>(propAgentId || null);\n";
    oss << "  const [agentDisplayNameState, setAgentDisplayNameState] = React.useState<string | null>(agentDisplayName || null);\n";
    oss << "  const [agentAvatarUrlState, setAgentAvatarUrlState] = React.useState<string | null>(agentAvatarUrl || null);\n\n";
    
    oss << "  // WebSocket connection to Bridge Server\n";
    oss << "  const { sendRequest, isConnected } = useWebSocket('ws://localhost:8080');\n\n";
    
    oss << "  // Attestation hook for task completion\n";
    oss << "  const { attestTaskCompletion } = useAttestation();\n\n";
    
    oss << "  // Agent launch state\n";
    oss << "  const [isLaunching, setIsLaunching] = React.useState(false);\n";
    oss << "  const [agentId, setAgentId] = React.useState<string | null>(null);\n";
    oss << "  const [status, setStatus] = React.useState<'idle' | 'running' | 'completed' | 'error'>('idle');\n";
    oss << "  const [progress, setProgress] = React.useState(0);\n";
    oss << "  const [error, setError] = React.useState<string | null>(null);\n\n";
    
    oss << "  // Launch agent via Bridge Server\n";
    oss << "  const handleLaunch = React.useCallback(async () => {\n";
    oss << "    if (!isConnected) {\n";
    oss << "      setError('Not connected to Bridge Server');\n";
    oss << "      return;\n";
    oss << "    }\n\n";
    
    oss << "    setIsLaunching(true);\n";
    oss << "    setStatus('running');\n";
    oss << "    setError(null);\n";
    oss << "    setProgress(0);\n\n";
    
    oss << "    try {\n";
    oss << "      // Send agent launch request via JSON-RPC\n";
    oss << "      const response = await sendRequest({\n";
    oss << "        jsonrpc: '2.0',\n";
    oss << "        id: Date.now(),\n";
    oss << "        method: 'nexus.agent.launch',\n";
    oss << "        params: {\n";
    oss << "          agentType: agentType,\n";
    oss << "          config: JSON.stringify({\n";
    oss << "            initial_query: taskDescription,\n";
    oss << "            max_results: config.maxResults || 10,\n";
    oss << "            timeout_seconds: config.timeoutSeconds || 300,\n";
    oss << "            task_id: taskId,\n";
    oss << "            ...config\n";
    oss << "          })\n";
    oss << "        }\n";
    oss << "      });\n\n";
    
    oss << "      if (response.error) {\n";
    oss << "        throw new Error(response.error.message || 'Agent launch failed');\n";
    oss << "      }\n\n";
    
    oss << "            const launchResult = JSON.parse(response.result || '{}');\n";
      oss << "      const newAgentId = launchResult.agentId;\n\n";
      
      oss << "      if (!newAgentId) {\n";
      oss << "        throw new Error('No agent ID returned');\n";
      oss << "      }\n\n";
      
      oss << "      setAgentId(newAgentId);\n";
      oss << "      setProgress(25);\n\n";
      
      oss << "      // Fetch agent profile to get avatar and display name\n";
      oss << "      try {\n";
      oss << "        const profileResponse = await sendRequest({\n";
      oss << "          jsonrpc: '2.0',\n";
      oss << "          id: Date.now(),\n";
      oss << "          method: 'nexus.agent.profile',\n";
      oss << "          params: { agentId: newAgentId }\n";
      oss << "        });\n\n";
      
      oss << "        if (!profileResponse.error && profileResponse.result) {\n";
      oss << "          const profile = JSON.parse(profileResponse.result);\n";
      oss << "          if (profile.displayName) {\n";
      oss << "            setAgentDisplayNameState(profile.displayName);\n";
      oss << "          }\n";
      oss << "          if (profile.avatarUrl) {\n";
      oss << "            setAgentAvatarUrlState(profile.avatarUrl);\n";
      oss << "          } else if (profile.displayName) {\n";
      oss << "            // Generate deterministic avatar if not provided\n";
      oss << "            // Avatar generation happens server-side, but we can show fallback\n";
      oss << "          }\n";
      oss << "        }\n";
      oss << "      } catch (profileErr) {\n";
      oss << "        console.warn('Failed to fetch agent profile:', profileErr);\n";
      oss << "        // Set default display name if profile fetch fails\n";
      oss << "        setAgentDisplayNameState('Agent ' + newAgentId.substring(0, 8));\n";
      oss << "      }\n\n";
    
    oss << "      // Poll agent status until completion\n";
    oss << "      const pollStatus = async () => {\n";
    oss << "        const statusResponse = await sendRequest({\n";
    oss << "          jsonrpc: '2.0',\n";
    oss << "          id: Date.now(),\n";
    oss << "          method: 'nexus.agent.status',\n";
    oss << "          params: { agentId: newAgentId }\n";
    oss << "        });\n\n";
    
    oss << "        if (statusResponse.error) {\n";
    oss << "          throw new Error(statusResponse.error.message || 'Status check failed');\n";
    oss << "        }\n\n";
    
    oss << "        const statusData = JSON.parse(statusResponse.result || '{}');\n";
    oss << "        const agentStatus = statusData.status;\n\n";
    
    oss << "        if (agentStatus === 'running') {\n";
    oss << "          setProgress(prev => Math.min(prev + 10, 90));\n";
    oss << "          setTimeout(pollStatus, 2000); // Poll every 2 seconds\n";
    oss << "        } else if (agentStatus === 'stopped' || agentStatus === 'completed') {\n";
    oss << "          setStatus('completed');\n";
    oss << "          setProgress(100);\n\n";
    
    oss << "          // Attest task completion\n";
    oss << "          try {\n";
    oss << "            await attestTaskCompletion({\n";
    oss << "              taskId: taskId,\n";
    oss << "              agentId: newAgentId,\n";
    oss << "              taskDescription: taskDescription,\n";
    oss << "              completionStatus: 'success',\n";
    oss << "              metadata: {\n";
    oss << "                agentType: agentType,\n";
    oss << "                completedAt: new Date().toISOString()\n";
    oss << "              }\n";
    oss << "            });\n";
    oss << "          } catch (attestError) {\n";
    oss << "            console.error('Attestation failed:', attestError);\n";
    oss << "            // Continue even if attestation fails\n";
    oss << "          }\n\n";
    
    oss << "          if (onComplete) {\n";
    oss << "            onComplete({ agentId: newAgentId, success: true });\n";
    oss << "          }\n";
    oss << "        } else if (agentStatus === 'error') {\n";
    oss << "          setStatus('error');\n";
    oss << "          setError(statusData.errorMessage || 'Agent execution failed');\n";
    oss << "          setProgress(0);\n\n";
    
    oss << "          // Attest failure\n";
    oss << "          try {\n";
    oss << "            await attestTaskCompletion({\n";
    oss << "              taskId: taskId,\n";
    oss << "              agentId: newAgentId,\n";
    oss << "              taskDescription: taskDescription,\n";
    oss << "              completionStatus: 'error',\n";
    oss << "              metadata: {\n";
    oss << "                agentType: agentType,\n";
    oss << "                error: statusData.errorMessage,\n";
    oss << "                completedAt: new Date().toISOString()\n";
    oss << "              }\n";
    oss << "            });\n";
    oss << "          } catch (attestError) {\n";
    oss << "            console.error('Attestation failed:', attestError);\n";
    oss << "          }\n\n";
    
    oss << "          if (onComplete) {\n";
    oss << "            onComplete({ agentId: newAgentId, success: false });\n";
    oss << "          }\n";
    oss << "        }\n";
    oss << "      };\n\n";
    
    oss << "      // Start polling\n";
    oss << "      setTimeout(pollStatus, 2000);\n";
    
    oss << "    } catch (err) {\n";
    oss << "      setStatus('error');\n";
    oss << "      setError(err instanceof Error ? err.message : 'Unknown error');\n";
    oss << "      setProgress(0);\n";
    oss << "    } finally {\n";
    oss << "      setIsLaunching(false);\n";
    oss << "    }\n";
    oss << "  }, [taskId, taskDescription, agentType, config, isConnected, sendRequest, attestTaskCompletion, onComplete]);\n\n";
    
    oss << "  return (\n";
    oss << "    <div className={cn('flex flex-col gap-2', className)}>\n";
    oss << "      {agentId && agentDisplayNameState && (\n";
    oss << "        <div className=\"flex items-center gap-2 mb-2\">\n";
    oss << "          <Avatar.Root className=\"w-10 h-10 rounded-full overflow-hidden border-2 border-gray-200\">\n";
    oss << "            {agentAvatarUrlState ? (\n";
    oss << "              <Avatar.Image src={agentAvatarUrlState} alt={agentDisplayNameState} className=\"object-cover\" />\n";
    oss << "            ) : null}\n";
    oss << "            <Avatar.Fallback className=\"w-full h-full flex items-center justify-center bg-gradient-to-br from-blue-400 to-purple-500 text-white font-semibold\">\n";
    oss << "              {agentDisplayNameState.charAt(0).toUpperCase()}\n";
    oss << "            </Avatar.Fallback>\n";
    oss << "          </Avatar.Root>\n";
    oss << "          <div className=\"flex flex-col\">\n";
    oss << "            <span className=\"text-sm font-medium text-gray-900\">{agentDisplayNameState}</span>\n";
    oss << "            <span className=\"text-xs text-gray-500\">Agent ID: {agentId.substring(0, 8)}...</span>\n";
    oss << "          </div>\n";
    oss << "        </div>\n";
    oss << "      )}\n";
    oss << "      <Button.Root\n";
    oss << "        onClick={handleLaunch}\n";
    oss << "        disabled={isLaunching || !isConnected || status === 'running'}\n";
    oss << "        className={cn(\n";
    oss << "          'inline-flex items-center justify-center rounded-md px-4 py-2',\n";
    oss << "          'text-sm font-medium transition-colors',\n";
    oss << "          'focus:outline-none focus:ring-2 focus:ring-offset-2',\n";
    oss << "          status === 'running' ? 'bg-blue-500 text-white' :\n";
    oss << "          status === 'completed' ? 'bg-green-500 text-white' :\n";
    oss << "          status === 'error' ? 'bg-red-500 text-white' :\n";
    oss << "          'bg-primary text-primary-foreground hover:bg-primary/90',\n";
    oss << "          (isLaunching || !isConnected || status === 'running') && 'opacity-50 cursor-not-allowed'\n";
    oss << "        )}\n";
    oss << "        aria-label=\"Launch agent for task\"\n";
    oss << "      >\n";
    oss << "        {status === 'idle' && 'Launch Agent'}\n";
    oss << "        {status === 'running' && 'Running...'}\n";
    oss << "        {status === 'completed' && 'Completed'}\n";
    oss << "        {status === 'error' && 'Retry'}\n";
    oss << "      </Button.Root>\n\n";
    
    oss << "      {status === 'running' && (\n";
    oss << "        <Progress.Root\n";
    oss << "          value={progress}\n";
    oss << "          className=\"w-full h-2 bg-gray-200 rounded-full overflow-hidden\"\n";
    oss << "        >\n";
    oss << "          <Progress.Indicator\n";
    oss << "            className=\"h-full bg-blue-500 transition-all duration-300\"\n";
    oss << "            style={{ width: `${progress}%` }}\n";
    oss << "          />\n";
    oss << "        </Progress.Root>\n";
    oss << "      )}\n\n";
    
    oss << "      {error && (\n";
    oss << "        <div className=\"text-sm text-red-600 bg-red-50 p-2 rounded\">\n";
    oss << "          {error}\n";
    oss << "        </div>\n";
    oss << "      )}\n\n";
    
    oss << "      {agentId && status === 'completed' && (\n";
    oss << "        <div className=\"text-sm text-gray-600\">\n";
    oss << "          Agent ID: {agentId}\n";
    oss << "        </div>\n";
    oss << "      )}\n";
    
    oss << "    </div>\n";
    oss << "  );\n";
    oss << "};\n";
    
    return oss.str();
}

// Generate WebSocket client hook for Bridge Server communication
std::string generate_websocket_client_hook() {
    std::ostringstream oss;
    
    oss << "import { useEffect, useRef, useState, useCallback } from 'react';\n\n";
    
    oss << "interface JsonRpcRequest {\n";
    oss << "  jsonrpc: '2.0';\n";
    oss << "  id: number;\n";
    oss << "  method: string;\n";
    oss << "  params?: Record<string, any>;\n";
    oss << "}\n\n";
    
    oss << "interface JsonRpcResponse {\n";
    oss << "  jsonrpc: '2.0';\n";
    oss << "  id: number;\n";
    oss << "  result?: string;\n";
    oss << "  error?: { code: number; message: string; data?: any };\n";
    oss << "}\n\n";
    
    oss << "export function useWebSocket(url: string) {\n";
    oss << "  const [isConnected, setIsConnected] = useState(false);\n";
    oss << "  const wsRef = useRef<WebSocket | null>(null);\n";
    oss << "  const requestQueueRef = useRef<Map<number, (response: JsonRpcResponse) => void>>(new Map());\n";
    oss << "  const requestIdRef = useRef(0);\n\n";
    
    oss << "  const connect = useCallback(() => {\n";
    oss << "    if (wsRef.current?.readyState === WebSocket.OPEN) {\n";
    oss << "      return;\n";
    oss << "    }\n\n";
    
    oss << "    const ws = new WebSocket(url);\n\n";
    
    oss << "    ws.onopen = () => {\n";
    oss << "      setIsConnected(true);\n";
    oss << "    };\n\n";
    
    oss << "    ws.onmessage = (event) => {\n";
    oss << "      try {\n";
    oss << "        const response: JsonRpcResponse = JSON.parse(event.data);\n";
    oss << "        const handler = requestQueueRef.current.get(response.id);\n";
    oss << "        if (handler) {\n";
    oss << "          handler(response);\n";
    oss << "          requestQueueRef.current.delete(response.id);\n";
    oss << "        }\n";
    oss << "      } catch (err) {\n";
    oss << "        console.error('Failed to parse WebSocket message:', err);\n";
    oss << "      }\n";
    oss << "    };\n\n";
    
    oss << "    ws.onerror = (error) => {\n";
    oss << "      console.error('WebSocket error:', error);\n";
    oss << "      setIsConnected(false);\n";
    oss << "    };\n\n";
    
    oss << "    ws.onclose = () => {\n";
    oss << "      setIsConnected(false);\n";
    oss << "      // Reconnect after 3 seconds\n";
    oss << "      setTimeout(connect, 3000);\n";
    oss << "    };\n\n";
    
    oss << "    wsRef.current = ws;\n";
    oss << "  }, [url]);\n\n";
    
    oss << "  const sendRequest = useCallback((request: JsonRpcRequest): Promise<JsonRpcResponse> => {\n";
    oss << "    return new Promise((resolve, reject) => {\n";
    oss << "      if (!wsRef.current || wsRef.current.readyState !== WebSocket.OPEN) {\n";
    oss << "        reject(new Error('WebSocket not connected'));\n";
    oss << "        return;\n";
    oss << "      }\n\n";
    
    oss << "      const id = requestIdRef.current++;\n";
    oss << "      const requestWithId = { ...request, id };\n\n";
    
    oss << "      requestQueueRef.current.set(id, resolve);\n\n";
    
    oss << "      // Timeout after 30 seconds\n";
    oss << "      setTimeout(() => {\n";
    oss << "        if (requestQueueRef.current.has(id)) {\n";
    oss << "          requestQueueRef.current.delete(id);\n";
    oss << "          reject(new Error('Request timeout'));\n";
    oss << "        }\n";
    oss << "      }, 30000);\n\n";
    
    oss << "      wsRef.current.send(JSON.stringify(requestWithId));\n";
    oss << "    });\n";
    oss << "  }, []);\n\n";
    
    oss << "  useEffect(() => {\n";
    oss << "    connect();\n";
    oss << "    return () => {\n";
    oss << "      if (wsRef.current) {\n";
    oss << "        wsRef.current.close();\n";
    oss << "      }\n";
    oss << "    };\n";
    oss << "  }, [connect]);\n\n";
    
    oss << "  return { sendRequest, isConnected };\n";
    oss << "}\n";
    
    return oss.str();
}

// Generate attestation hook for task completion
std::string generate_attestation_hook() {
    std::ostringstream oss;
    
    oss << "import { useCallback } from 'react';\n";
    oss << "import { useWebSocket } from './useWebSocket';\n\n";
    
    oss << "interface AttestationRequest {\n";
    oss << "  taskId: string;\n";
    oss << "  agentId: string;\n";
    oss << "  taskDescription: string;\n";
    oss << "  completionStatus: 'success' | 'error';\n";
    oss << "  metadata?: Record<string, any>;\n";
    oss << "}\n\n";
    
    oss << "export function useAttestation() {\n";
    oss << "  const { sendRequest } = useWebSocket('ws://localhost:8080');\n\n";
    
    oss << "  const attestTaskCompletion = useCallback(async (request: AttestationRequest): Promise<void> => {\n";
    oss << "    try {\n";
    oss << "      const response = await sendRequest({\n";
    oss << "        jsonrpc: '2.0',\n";
    oss << "        id: Date.now(),\n";
    oss << "        method: 'nexus.attestation.create',\n";
    oss << "        params: {\n";
    oss << "          taskId: request.taskId,\n";
    oss << "          agentId: request.agentId,\n";
    oss << "          taskDescription: request.taskDescription,\n";
    oss << "          completionStatus: request.completionStatus,\n";
    oss << "          metadata: JSON.stringify(request.metadata || {})\n";
    oss << "        }\n";
    oss << "      });\n\n";
    
    oss << "      if (response.error) {\n";
    oss << "        throw new Error(response.error.message || 'Attestation failed');\n";
    oss << "      }\n\n";
    
    oss << "      console.log('Task completion attested:', request.taskId);\n";
    oss << "    } catch (err) {\n";
    oss << "      console.error('Attestation error:', err);\n";
    oss << "      throw err;\n";
    oss << "    }\n";
    oss << "  }, [sendRequest]);\n\n";
    
    oss << "  return { attestTaskCompletion };\n";
    oss << "}\n";
    
    return oss.str();
}

// Check if component has nexus_agent_launch attribute
bool has_nexus_agent_launch(const CppStruct& component_def) {
    // This would be checked during parsing - for now return false
    // In real implementation, check for [[nexus_agent_launch]] attribute
    return false;
}

// Extract agent launch task from component
AgentLaunchTask extract_agent_task(const CppStruct& component_def) {
    AgentLaunchTask task;
    task.task_id = component_def.name + "-task";
    task.task_description = "Task for " + component_def.name;
    task.agent_type = "research";
    task.requires_attestation = true;
    return task;
}

// Generate complete agent launch component with status tracking
std::string generate_agent_launch_component(const CppStruct& component_def) {
    AgentLaunchTask task = extract_agent_task(component_def);
    return generate_agent_launch_button(task, component_def.name + "AgentLaunch");
}

} // namespace nexus_integration
