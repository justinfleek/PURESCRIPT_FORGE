"""
Nexus Agent Orchestrator
Launch and manage autonomous agents in bubblewrap sandboxes
"""

# Legacy bubblewrap support (deprecated)
from .sandbox_manager import SandboxManager, Sandbox, AgentType, SandboxProfile, DirectoryAccess
from .launcher import AgentLauncher, AgentConfig, AgentStatus
from .manager import AgentManager
from .coordinator import AgentCoordinator, CoordinationPlan
from .monitor import AgentMonitor, AgentHealth

# gVisor support (new, preferred)
from .gvisor_sandbox_manager import GVisorSandboxManager, GVisorSandbox
from .gvisor_launcher import GVisorAgentLauncher

__all__ = [
    # Legacy bubblewrap
    "SandboxManager",
    "Sandbox",
    "AgentType",
    "SandboxProfile",
    "DirectoryAccess",
    "AgentLauncher",
    "AgentConfig",
    "AgentStatus",
    "AgentManager",
    "AgentCoordinator",
    "CoordinationPlan",
    "AgentMonitor",
    "AgentHealth",
    # gVisor (preferred)
    "GVisorSandboxManager",
    "GVisorSandbox",
    "GVisorAgentLauncher",
]
