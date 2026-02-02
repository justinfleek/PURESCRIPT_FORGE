"""
Nexus Agent Orchestrator - Agent Coordinator
Coordinates agent interactions and workflows
"""

from typing import List, Dict, Any, Optional
from dataclasses import dataclass
from .manager import AgentManager
from .launcher import AgentType, AgentConfig


@dataclass
class CoordinationPlan:
    """Coordination plan for multiple agents"""
    workflow: str  # web_search_to_network, content_extraction_to_network, etc.
    agent_sequence: List[str]  # Agent IDs in execution order
    dependencies: Dict[str, List[str]]  # Agent ID -> List of dependency agent IDs


class AgentCoordinator:
    """
    Agent coordinator for coordinating agent interactions.
    
    Manages multi-agent workflows and agent dependencies.
    """
    
    def __init__(self, manager: AgentManager):
        """
        Initialize agent coordinator.
        
        Args:
            manager: Agent manager instance
        """
        self.manager = manager
        self.workflows: Dict[str, List[str]] = {}
    
    def coordinate_agents(
        self,
        agent_ids: List[str],
        workflow: str = "parallel"
    ) -> CoordinationPlan:
        """
        Coordinate multiple agents.
        
        Args:
            agent_ids: List of agent IDs to coordinate
            workflow: Workflow type (parallel, sequential, web_search_to_network, etc.)
            
        Returns:
            Coordination plan
        """
        if workflow == "parallel":
            # All agents run in parallel
            dependencies = {}
        elif workflow == "sequential":
            # Agents run one after another
            dependencies = {
                agent_ids[i]: [agent_ids[i-1]] if i > 0 else []
                for i in range(len(agent_ids))
            }
        elif workflow == "web_search_to_network":
            # Web search agents -> Content extraction -> Network formation
            web_search_ids = [aid for aid in agent_ids if self._is_agent_type(aid, AgentType.WEB_SEARCH)]
            content_ids = [aid for aid in agent_ids if self._is_agent_type(aid, AgentType.CONTENT_EXTRACTION)]
            network_ids = [aid for aid in agent_ids if self._is_agent_type(aid, AgentType.NETWORK_FORMATION)]
            
            dependencies = {}
            for cid in content_ids:
                dependencies[cid] = web_search_ids
            for nid in network_ids:
                dependencies[nid] = content_ids + web_search_ids
        else:
            dependencies = {}
        
        plan = CoordinationPlan(
            workflow=workflow,
            agent_sequence=agent_ids,
            dependencies=dependencies
        )
        
        self.workflows[workflow] = agent_ids
        return plan
    
    def _is_agent_type(self, agent_id: str, agent_type: AgentType) -> bool:
        """Check if agent is of given type"""
        status = self.manager.get_status(agent_id)
        return status is not None and status.agent_type == agent_type
    
    def execute_workflow(self, workflow: str) -> None:
        """
        Execute workflow.
        
        Args:
            workflow: Workflow name
        """
        if workflow not in self.workflows:
            raise ValueError(f"Workflow {workflow} not found")
        
        agent_ids = self.workflows[workflow]
        plan = self.coordinate_agents(agent_ids, workflow)
        
        # Execute based on dependencies
        executed = set()
        
        def execute_agent(aid: str):
            if aid in executed:
                return
            
            # Execute dependencies first
            for dep_id in plan.dependencies.get(aid, []):
                execute_agent(dep_id)
            
            # Start agent if not running
            status = self.manager.get_status(aid)
            if status is None or status.status != "running":
                # Would restart agent here
                pass
            
            executed.add(aid)
        
        # Execute all agents
        for agent_id in plan.agent_sequence:
            execute_agent(agent_id)
