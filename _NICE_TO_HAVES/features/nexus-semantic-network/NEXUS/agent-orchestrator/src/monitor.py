"""
Nexus Agent Orchestrator - Agent Monitor
Monitors agent health and performance
"""

import time
from typing import List, Dict, Any, Optional
from dataclasses import dataclass
from datetime import datetime, timedelta
from .manager import AgentManager
from .launcher import AgentStatus


@dataclass
class AgentHealth:
    """Agent health metrics"""
    agent_id: str
    status: str
    uptime_seconds: float
    cpu_percent: Optional[float] = None
    memory_mb: Optional[float] = None
    last_heartbeat: Optional[str] = None
    error_count: int = 0


class AgentMonitor:
    """
    Agent monitor for monitoring agent health and performance.
    
    Tracks agent status, resource usage, and errors.
    """
    
    def __init__(self, manager: AgentManager, check_interval: float = 5.0):
        """
        Initialize agent monitor.
        
        Args:
            manager: Agent manager instance
            check_interval: Health check interval in seconds
        """
        self.manager = manager
        self.check_interval = check_interval
        self.health_history: Dict[str, List[AgentHealth]] = {}
        self.error_counts: Dict[str, int] = {}
        self.start_times: Dict[str, datetime] = {}
    
    def check_agent_health(self, agent_id: str) -> Optional[AgentHealth]:
        """
        Check agent health.
        
        Args:
            agent_id: Agent ID
            
        Returns:
            Agent health or None if agent not found
        """
        status = self.manager.get_status(agent_id)
        if status is None:
            return None
        
        # Calculate uptime
        uptime = 0.0
        if agent_id in self.start_times:
            uptime = (datetime.utcnow() - self.start_times[agent_id]).total_seconds()
        
        # Get error count
        error_count = self.error_counts.get(agent_id, 0)
        
        health = AgentHealth(
            agent_id=agent_id,
            status=status.status,
            uptime_seconds=uptime,
            cpu_percent=None,  # Would get from process if available
            memory_mb=None,  # Would get from process if available
            last_heartbeat=datetime.utcnow().isoformat(),
            error_count=error_count
        )
        
        # Store health history
        if agent_id not in self.health_history:
            self.health_history[agent_id] = []
        self.health_history[agent_id].append(health)
        
        # Keep only last 100 health checks
        if len(self.health_history[agent_id]) > 100:
            self.health_history[agent_id] = self.health_history[agent_id][-100:]
        
        return health
    
    def check_all_agents(self) -> Dict[str, AgentHealth]:
        """
        Check health of all agents.
        
        Returns:
            Dictionary mapping agent ID to health
        """
        agent_ids = self.manager.list_agents()
        health_status = {}
        
        for agent_id in agent_ids:
            health = self.check_agent_health(agent_id)
            if health:
                health_status[agent_id] = health
        
        return health_status
    
    def record_error(self, agent_id: str) -> None:
        """
        Record error for agent.
        
        Args:
            agent_id: Agent ID
        """
        self.error_counts[agent_id] = self.error_counts.get(agent_id, 0) + 1
    
    def get_health_history(self, agent_id: str, limit: int = 100) -> List[AgentHealth]:
        """
        Get health history for agent.
        
        Args:
            agent_id: Agent ID
            limit: Maximum number of records to return
            
        Returns:
            List of health records
        """
        return self.health_history.get(agent_id, [])[-limit:]
    
    def detect_unhealthy_agents(self, max_errors: int = 5) -> List[str]:
        """
        Detect unhealthy agents (high error count).
        
        Args:
            max_errors: Maximum errors before considered unhealthy
            
        Returns:
            List of unhealthy agent IDs
        """
        unhealthy = []
        
        for agent_id, error_count in self.error_counts.items():
            if error_count >= max_errors:
                unhealthy.append(agent_id)
        
        return unhealthy
    
    def detect_stopped_agents(self) -> List[str]:
        """
        Detect stopped agents that should be running.
        
        Returns:
            List of stopped agent IDs
        """
        stopped = []
        
        for agent_id in self.manager.list_agents():
            status = self.manager.get_status(agent_id)
            if status and status.status == "stopped":
                stopped.append(agent_id)
        
        return stopped
