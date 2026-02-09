"""
Nexus Agent Orchestrator - Sandbox Manager
Creates and manages bubblewrap sandboxes for agent isolation
"""

import subprocess
import json
import os
from pathlib import Path
from typing import List, Optional, Dict, Any
from dataclasses import dataclass, asdict
from enum import Enum
import uuid


class AgentType(Enum):
    """Agent type"""
    WEB_SEARCH = "web_search"
    CONTENT_EXTRACTION = "content_extraction"
    NETWORK_FORMATION = "network_formation"
    DATABASE_LAYER = "database_layer"


@dataclass
class DirectoryAccess:
    """Directory access configuration"""
    host_path: str
    sandbox_path: str
    read_only: bool


@dataclass
class SandboxProfile:
    """Sandbox profile for an agent type"""
    agent_type: AgentType
    allowed_dirs: List[DirectoryAccess]
    network_access: bool
    working_dir: str
    shared_dirs: List[str]


@dataclass
class Sandbox:
    """Sandbox instance"""
    agent_id: str
    agent_type: AgentType
    profile: SandboxProfile
    process: Optional[subprocess.Popen] = None


class SandboxManager:
    """
    Sandbox manager for creating and managing bubblewrap sandboxes.
    
    All agents run in isolated bubblewrap sandboxes with restricted folder access.
    """
    
    def __init__(self, base_dir: str = "/tmp/nexus"):
        """
        Initialize sandbox manager.
        
        Args:
            base_dir: Base directory for Nexus data
        """
        self.base_dir = Path(base_dir)
        self.base_dir.mkdir(parents=True, exist_ok=True)
        
        # Create directory structure
        self._setup_directories()
        
        # Load sandbox profiles
        self.profiles = self._load_profiles()
    
    def _setup_directories(self) -> None:
        """Create directory structure with correct permissions"""
        # Agent directories
        (self.base_dir / "agents").mkdir(exist_ok=True)
        (self.base_dir / "agents").chmod(0o755)
        
        # Shared directories
        (self.base_dir / "shared" / "semantic-memory").mkdir(parents=True, exist_ok=True)
        (self.base_dir / "shared" / "semantic-memory").chmod(0o755)
        
        (self.base_dir / "shared" / "network-graph").mkdir(parents=True, exist_ok=True)
        (self.base_dir / "shared" / "network-graph").chmod(0o755)
        
        (self.base_dir / "shared" / "content").mkdir(parents=True, exist_ok=True)
        (self.base_dir / "shared" / "content").chmod(0o755)
        
        # Database directory
        (self.base_dir / "database").mkdir(exist_ok=True)
        (self.base_dir / "database").chmod(0o700)
    
    def _load_profiles(self) -> Dict[AgentType, SandboxProfile]:
        """Load sandbox profiles for each agent type"""
        profiles = {}
        
        # Web Search Agent Profile
        profiles[AgentType.WEB_SEARCH] = SandboxProfile(
            agent_type=AgentType.WEB_SEARCH,
            allowed_dirs=[
                DirectoryAccess(
                    host_path=str(self.base_dir / "agents" / "{agent_id}"),
                    sandbox_path="/tmp/nexus/agents/{agent_id}",
                    read_only=False
                ),
                DirectoryAccess(
                    host_path=str(self.base_dir / "shared" / "content"),
                    sandbox_path="/tmp/nexus/shared/content",
                    read_only=False
                ),
                DirectoryAccess(
                    host_path=str(self.base_dir / "shared" / "semantic-memory"),
                    sandbox_path="/tmp/nexus/shared/semantic-memory",
                    read_only=True
                ),
            ],
            network_access=True,
            working_dir="/tmp/nexus/agents/{agent_id}",
            shared_dirs=[
                "/tmp/nexus/shared/content",
                "/tmp/nexus/shared/semantic-memory"
            ]
        )
        
        # Content Extraction Agent Profile
        profiles[AgentType.CONTENT_EXTRACTION] = SandboxProfile(
            agent_type=AgentType.CONTENT_EXTRACTION,
            allowed_dirs=[
                DirectoryAccess(
                    host_path=str(self.base_dir / "agents" / "{agent_id}"),
                    sandbox_path="/tmp/nexus/agents/{agent_id}",
                    read_only=False
                ),
                DirectoryAccess(
                    host_path=str(self.base_dir / "shared" / "content"),
                    sandbox_path="/tmp/nexus/shared/content",
                    read_only=True
                ),
                DirectoryAccess(
                    host_path=str(self.base_dir / "shared" / "semantic-memory"),
                    sandbox_path="/tmp/nexus/shared/semantic-memory",
                    read_only=False
                ),
            ],
            network_access=False,
            working_dir="/tmp/nexus/agents/{agent_id}",
            shared_dirs=[
                "/tmp/nexus/shared/content",
                "/tmp/nexus/shared/semantic-memory"
            ]
        )
        
        # Network Formation Agent Profile
        profiles[AgentType.NETWORK_FORMATION] = SandboxProfile(
            agent_type=AgentType.NETWORK_FORMATION,
            allowed_dirs=[
                DirectoryAccess(
                    host_path=str(self.base_dir / "agents" / "{agent_id}"),
                    sandbox_path="/tmp/nexus/agents/{agent_id}",
                    read_only=False
                ),
                DirectoryAccess(
                    host_path=str(self.base_dir / "shared" / "semantic-memory"),
                    sandbox_path="/tmp/nexus/shared/semantic-memory",
                    read_only=True
                ),
                DirectoryAccess(
                    host_path=str(self.base_dir / "shared" / "network-graph"),
                    sandbox_path="/tmp/nexus/shared/network-graph",
                    read_only=False
                ),
            ],
            network_access=False,
            working_dir="/tmp/nexus/agents/{agent_id}",
            shared_dirs=[
                "/tmp/nexus/shared/semantic-memory",
                "/tmp/nexus/shared/network-graph"
            ]
        )
        
        # Database Layer Profile
        profiles[AgentType.DATABASE_LAYER] = SandboxProfile(
            agent_type=AgentType.DATABASE_LAYER,
            allowed_dirs=[
                DirectoryAccess(
                    host_path=str(self.base_dir / "database"),
                    sandbox_path="/tmp/nexus/database",
                    read_only=False
                ),
                DirectoryAccess(
                    host_path=str(self.base_dir / "shared" / "semantic-memory"),
                    sandbox_path="/tmp/nexus/shared/semantic-memory",
                    read_only=False
                ),
                DirectoryAccess(
                    host_path=str(self.base_dir / "shared" / "network-graph"),
                    sandbox_path="/tmp/nexus/shared/network-graph",
                    read_only=False
                ),
                DirectoryAccess(
                    host_path=str(self.base_dir / "shared" / "content"),
                    sandbox_path="/tmp/nexus/shared/content",
                    read_only=False
                ),
            ],
            network_access=False,
            working_dir="/tmp/nexus/database",
            shared_dirs=[
                "/tmp/nexus/shared/semantic-memory",
                "/tmp/nexus/shared/network-graph",
                "/tmp/nexus/shared/content"
            ]
        )
        
        return profiles
    
    def get_sandbox_profile(self, agent_type: AgentType) -> SandboxProfile:
        """
        Get sandbox profile for agent type.
        
        Args:
            agent_type: Agent type
            
        Returns:
            Sandbox profile
        """
        return self.profiles[agent_type]
    
    def create_sandbox(
        self,
        agent_type: AgentType,
        agent_id: str,
        config: Optional[Dict[str, Any]] = None
    ) -> Sandbox:
        """
        Create sandbox for agent.
        
        Args:
            agent_type: Agent type
            agent_id: Agent ID
            config: Optional sandbox configuration
            
        Returns:
            Sandbox instance
        """
        profile = self.get_sandbox_profile(agent_type)
        
        # Create agent working directory
        agent_dir = self.base_dir / "agents" / agent_id
        agent_dir.mkdir(parents=True, exist_ok=True)
        agent_dir.chmod(0o700)  # Owner only
        
        return Sandbox(
            agent_id=agent_id,
            agent_type=agent_type,
            profile=profile
        )
    
    def build_bwrap_command(self, sandbox: Sandbox, command: List[str]) -> List[str]:
        """
        Build bubblewrap command for sandbox.
        
        Args:
            sandbox: Sandbox instance
            command: Command to run in sandbox
            
        Returns:
            bwrap command as list of strings
        """
        profile = sandbox.profile
        agent_id = sandbox.agent_id
        
        # Start with bwrap command
        bwrap_cmd = ["bwrap"]
        
        # Add directory bindings
        for dir_access in profile.allowed_dirs:
            host_path = dir_access.host_path.format(agent_id=agent_id)
            sandbox_path = dir_access.sandbox_path.format(agent_id=agent_id)
            
            if dir_access.read_only:
                bwrap_cmd.extend(["--ro-bind", host_path, sandbox_path])
            else:
                bwrap_cmd.extend(["--bind", host_path, sandbox_path])
        
        # Namespace isolation
        bwrap_cmd.extend([
            "--unshare-ipc",
            "--unshare-pid",
            "--unshare-uts",
        ])
        
        # Network access control
        if not profile.network_access:
            bwrap_cmd.append("--unshare-net")
        
        # Process control
        bwrap_cmd.extend([
            "--die-with-parent",
            "--new-session",
        ])
        
        # Change to working directory
        working_dir = profile.working_dir.format(agent_id=agent_id)
        bwrap_cmd.extend(["--chdir", working_dir])
        
        # Add command to execute
        bwrap_cmd.extend(command)
        
        return bwrap_cmd
    
    def launch_in_sandbox(
        self,
        sandbox: Sandbox,
        command: List[str],
        env: Optional[Dict[str, str]] = None
    ) -> subprocess.Popen:
        """
        Launch command in sandbox.
        
        Args:
            sandbox: Sandbox instance
            command: Command to run
            env: Optional environment variables
            
        Returns:
            Process handle
        """
        bwrap_cmd = self.build_bwrap_command(sandbox, command)
        
        # Prepare environment
        process_env = os.environ.copy()
        if env:
            process_env.update(env)
        
        # Launch process
        process = subprocess.Popen(
            bwrap_cmd,
            env=process_env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True
        )
        
        sandbox.process = process
        return process
    
    def destroy_sandbox(self, sandbox: Sandbox) -> None:
        """
        Destroy sandbox and cleanup.
        
        Args:
            sandbox: Sandbox instance
        """
        # Terminate process if running
        if sandbox.process:
            sandbox.process.terminate()
            try:
                sandbox.process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                sandbox.process.kill()
        
        # Cleanup agent directory (optional - may want to keep for debugging)
        # agent_dir = self.base_dir / "agents" / sandbox.agent_id
        # if agent_dir.exists():
        #     import shutil
        #     shutil.rmtree(agent_dir)
