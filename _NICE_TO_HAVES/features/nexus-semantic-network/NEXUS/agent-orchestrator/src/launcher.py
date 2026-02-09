"""
Nexus Agent Orchestrator - Agent Launcher
Launches agents in bubblewrap sandboxes
"""

import uuid
from typing import Optional, Dict, Any, List
from dataclasses import dataclass
from datetime import datetime
from .sandbox_manager import SandboxManager, AgentType, Sandbox


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
    error_message: Optional[str] = None


class AgentLauncher:
    """
    Agent launcher for launching agents in sandboxes.
    
    All agents are launched in isolated bubblewrap sandboxes.
    """
    
    def __init__(self, sandbox_manager: SandboxManager):
        """
        Initialize agent launcher.
        
        Args:
            sandbox_manager: Sandbox manager instance
        """
        self.sandbox_manager = sandbox_manager
        self.active_agents: Dict[str, Sandbox] = {}
    
    def launch_agent(
        self,
        agent_type: AgentType,
        config: AgentConfig,
        agent_id: Optional[str] = None
    ) -> str:
        """
        Launch agent in sandbox.
        
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
        
        # Launch in sandbox
        process = self.sandbox_manager.launch_in_sandbox(sandbox, command)
        
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
            return [
                "python3",
                "-m", "nexus.web_search_agent",
                "--query", config.initial_query or "",
                "--max-results", str(config.max_results),
                "--timeout", str(config.timeout_seconds)
            ]
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
            process_id=process_id
        )
    
    def list_agents(self) -> List[str]:
        """
        List active agent IDs.
        
        Returns:
            List of agent IDs
        """
        return list(self.active_agents.keys())
