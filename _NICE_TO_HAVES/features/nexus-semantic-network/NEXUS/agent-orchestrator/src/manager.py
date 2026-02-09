"""
Nexus Agent Orchestrator - Agent Manager
Manages agent lifecycle (start, stop, restart, monitor)
"""

from typing import List, Optional, Dict, Any
from datetime import datetime
from .launcher import AgentLauncher, AgentConfig, AgentStatus, AgentType
from .sandbox_manager import SandboxManager


class AgentManager:
    """
    Agent manager for managing agent lifecycle.
    
    Handles starting, stopping, restarting, and monitoring agents.
    """
    
    def __init__(self, launcher: AgentLauncher):
        """
        Initialize agent manager.
        
        Args:
            launcher: Agent launcher instance
        """
        self.launcher = launcher
        self.agent_configs: Dict[str, AgentConfig] = {}
        self.agent_start_times: Dict[str, str] = {}
    
    def start_agent(
        self,
        agent_type: AgentType,
        config: AgentConfig,
        agent_id: Optional[str] = None
    ) -> str:
        """
        Start agent.
        
        Args:
            agent_type: Agent type
            config: Agent configuration
            agent_id: Optional agent ID
            
        Returns:
            Agent ID
        """
        agent_id = self.launcher.launch_agent(agent_type, config, agent_id)
        self.agent_configs[agent_id] = config
        self.agent_start_times[agent_id] = datetime.utcnow().isoformat()
        return agent_id
    
    def stop_agent(self, agent_id: str) -> None:
        """
        Stop agent.
        
        Args:
            agent_id: Agent ID
        """
        self.launcher.stop_agent(agent_id)
        if agent_id in self.agent_configs:
            del self.agent_configs[agent_id]
        if agent_id in self.agent_start_times:
            del self.agent_start_times[agent_id]
    
    def restart_agent(self, agent_id: str) -> str:
        """
        Restart agent.
        
        Args:
            agent_id: Agent ID
            
        Returns:
            New agent ID (or same if restart successful)
        """
        if agent_id not in self.agent_configs:
            raise ValueError(f"Agent {agent_id} not found")
        
        config = self.agent_configs[agent_id]
        agent_type = self.launcher.get_agent_status(agent_id).agent_type
        
        # Stop old agent
        try:
            self.stop_agent(agent_id)
        except ValueError:
            pass  # Already stopped
        
        # Start new agent
        new_agent_id = self.start_agent(agent_type, config, agent_id)
        return new_agent_id
    
    def get_status(self, agent_id: str) -> Optional[AgentStatus]:
        """
        Get agent status.
        
        Args:
            agent_id: Agent ID
            
        Returns:
            Agent status or None if not found
        """
        return self.launcher.get_agent_status(agent_id)
    
    def list_agents(self) -> List[str]:
        """
        List all agent IDs.
        
        Returns:
            List of agent IDs
        """
        return self.launcher.list_agents()
    
    def list_agents_by_type(self, agent_type: AgentType) -> List[str]:
        """
        List agent IDs by type.
        
        Args:
            agent_type: Agent type
            
        Returns:
            List of agent IDs
        """
        all_agents = self.list_agents()
        return [
            agent_id for agent_id in all_agents
            if self.get_status(agent_id) and self.get_status(agent_id).agent_type == agent_type
        ]
    
    def list_agents_by_status(self, status: str) -> List[str]:
        """
        List agent IDs by status.
        
        Args:
            status: Status (running, stopped, error)
            
        Returns:
            List of agent IDs
        """
        all_agents = self.list_agents()
        return [
            agent_id for agent_id in all_agents
            if self.get_status(agent_id) and self.get_status(agent_id).status == status
        ]
