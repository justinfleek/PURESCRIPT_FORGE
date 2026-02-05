"""
Nexus Agent Orchestrator - gVisor Agent Launcher
Launches agents in gVisor containers
"""

import uuid
from typing import Optional, Dict, Any, List
from dataclasses import dataclass
from datetime import datetime
from .gvisor_sandbox_manager import GVisorSandboxManager, AgentType, GVisorSandbox


@dataclass
class AgentConfig:
    """Agent configuration"""
    initial_query: Optional[str] = None
    max_results: int = 10
    timeout_seconds: int = 300
    other: Optional[Dict[str, Any]] = None


@dataclass
class AgentStatus:
    """Agent status"""
    agent_id: str
    agent_type: AgentType
    status: str  # running, stopped, error
    started_at: str
    updated_at: str
    process_id: Optional[int] = None
    container_id: Optional[str] = None
    error_message: Optional[str] = None


class GVisorAgentLauncher:
    """
    Agent launcher for launching agents in gVisor containers.
    
    All agents are launched in isolated gVisor containers.
    """
    
    def __init__(self, sandbox_manager: GVisorSandboxManager):
        """
        Initialize agent launcher.
        
        Args:
            sandbox_manager: gVisor sandbox manager instance
        """
        self.sandbox_manager = sandbox_manager
        self.active_agents: Dict[str, GVisorSandbox] = {}
    
    def launch_agent(
        self,
        agent_type: AgentType,
        config: AgentConfig,
        agent_id: Optional[str] = None
    ) -> str:
        """
        Launch agent in gVisor container.
        
        Args:
            agent_type: Agent type
            config: Agent configuration
            agent_id: Optional agent ID (generated if not provided)
            
        Returns:
            Agent ID
        """
        # Generate agent ID if not provided
        if agent_id is None:
            agent_id = str(uuid.uuid4())
        
        # Create sandbox
        sandbox = self.sandbox_manager.create_sandbox(agent_type, agent_id)
        
        # Build command based on agent type
        command = self._build_agent_command(agent_type, config)
        
        # Prepare environment variables
        env = {
            "NEXUS_AGENT_ID": agent_id,
            "NEXUS_AGENT_TYPE": agent_type.value,
            "NEXUS_TIMEOUT": str(config.timeout_seconds),
        }
        if config.initial_query:
            env["NEXUS_QUERY"] = config.initial_query
        if config.max_results:
            env["NEXUS_MAX_RESULTS"] = str(config.max_results)
        if config.other:
            for k, v in config.other.items():
                env[f"NEXUS_{k.upper()}"] = str(v)
        
        # Launch in sandbox
        process = self.sandbox_manager.launch_in_sandbox(sandbox, command, env)
        
        # Store active agent
        self.active_agents[agent_id] = sandbox
        
        return agent_id
    
    def _build_agent_command(
        self,
        agent_type: AgentType,
        config: AgentConfig
    ) -> List[str]:
        """
        Build command for agent type.
        
        Args:
            agent_type: Agent type
            config: Agent configuration
            
        Returns:
            Command as list of strings
        """
        if agent_type == AgentType.WEB_SEARCH:
            cmd = [
                "python3",
                "-m", "nexus.web_search_agent",
            ]
            if config.initial_query:
                cmd.extend(["--query", config.initial_query])
            cmd.extend([
                "--max-results", str(config.max_results),
                "--timeout", str(config.timeout_seconds)
            ])
            return cmd
        elif agent_type == AgentType.CONTENT_EXTRACTION:
            return [
                "python3",
                "-m", "nexus.content_extraction_agent",
                "--timeout", str(config.timeout_seconds)
            ]
        elif agent_type == AgentType.NETWORK_FORMATION:
            return [
                "python3",
                "-m", "nexus.network_formation_agent",
                "--timeout", str(config.timeout_seconds)
            ]
        elif agent_type == AgentType.DATABASE_LAYER:
            return [
                "python3",
                "-m", "nexus.database_layer",
            ]
        else:
            raise ValueError(f"Unknown agent type: {agent_type}")
    
    def stop_agent(self, agent_id: str) -> None:
        """
        Stop agent.
        
        Args:
            agent_id: Agent ID
        """
        if agent_id not in self.active_agents:
            raise ValueError(f"Agent {agent_id} not found")
        
        sandbox = self.active_agents[agent_id]
        self.sandbox_manager.destroy_sandbox(sandbox)
        del self.active_agents[agent_id]
    
    def get_agent_status(self, agent_id: str) -> Optional[AgentStatus]:
        """
        Get agent status.
        
        Args:
            agent_id: Agent ID
            
        Returns:
            Agent status or None if not found
        """
        if agent_id not in self.active_agents:
            return None
        
        sandbox = self.active_agents[agent_id]
        process = sandbox.process
        
        if process is None:
            status = "stopped"
            process_id = None
        elif process.poll() is None:
            status = "running"
            process_id = process.pid
        else:
            status = "stopped"
            process_id = process.pid
        
        return AgentStatus(
            agent_id=agent_id,
            agent_type=sandbox.agent_type,
            status=status,
            started_at=datetime.utcnow().isoformat(),  # Would track actual start time
            updated_at=datetime.utcnow().isoformat(),
            process_id=process_id,
            container_id=sandbox.container_id
        )
    
    def list_agents(self) -> List[str]:
        """
        List active agent IDs.
        
        Returns:
            List of agent IDs
        """
        return list(self.active_agents.keys())
