"""
Nexus Agent Orchestrator - gVisor Sandbox Manager
Creates and manages gVisor containers for agent isolation
"""

import subprocess
import json
import os
import shutil
from pathlib import Path
from typing import List, Optional, Dict, Any
from dataclasses import dataclass
from enum import Enum
import uuid
import tempfile


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
class GVisorSandbox:
    """gVisor sandbox instance"""
    agent_id: str
    agent_type: AgentType
    profile: SandboxProfile
    container_id: Optional[str] = None
    bundle_path: Optional[str] = None
    process: Optional[subprocess.Popen] = None


class GVisorSandboxManager:
    """
    Sandbox manager for creating and managing gVisor containers.
    
    All agents run in isolated gVisor containers with restricted access.
    Uses runsc (gVisor runtime) for container management.
    """
    
    def __init__(
        self,
        base_dir: str = "/tmp/nexus",
        runsc_path: str = "/usr/local/bin/runsc",
        platform: str = "systrap"
    ):
        """
        Initialize gVisor sandbox manager.
        
        Args:
            base_dir: Base directory for Nexus data
            runsc_path: Path to runsc binary
            platform: gVisor platform (kvm, ptrace, systrap)
        """
        self.base_dir = Path(base_dir)
        self.runsc_path = runsc_path
        self.platform = platform
        self.base_dir.mkdir(parents=True, exist_ok=True)
        
        # Create directory structure
        self._setup_directories()
        
        # Load sandbox profiles
        self.profiles = self._load_profiles()
        
        # Verify runsc is available
        self._verify_runsc()
    
    def _verify_runsc(self) -> None:
        """Verify runsc binary is available"""
        if not os.path.exists(self.runsc_path):
            raise RuntimeError(
                f"gVisor runsc not found at {self.runsc_path}. "
                "Please install gVisor: https://gvisor.dev/docs/user_guide/install/"
            )
        
        # Test runsc
        try:
            result = subprocess.run(
                [self.runsc_path, "--version"],
                capture_output=True,
                text=True,
                timeout=5
            )
            if result.returncode != 0:
                raise RuntimeError(f"runsc version check failed: {result.stderr}")
        except FileNotFoundError:
            raise RuntimeError(f"runsc binary not executable: {self.runsc_path}")
    
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
    ) -> GVisorSandbox:
        """
        Create gVisor sandbox for agent.
        
        Args:
            agent_type: Agent type
            agent_id: Agent ID
            config: Optional sandbox configuration
            
        Returns:
            GVisor sandbox instance
        """
        profile = self.get_sandbox_profile(agent_type)
        
        # Create agent working directory
        agent_dir = self.base_dir / "agents" / agent_id
        agent_dir.mkdir(parents=True, exist_ok=True)
        agent_dir.chmod(0o700)  # Owner only
        
        # Generate container ID
        container_id = f"nexus-{agent_id}"
        
        return GVisorSandbox(
            agent_id=agent_id,
            agent_type=agent_type,
            profile=profile,
            container_id=container_id
        )
    
    def _create_oci_bundle(
        self,
        sandbox: GVisorSandbox,
        command: List[str],
        env: Optional[Dict[str, str]] = None
    ) -> str:
        """
        Create OCI bundle for gVisor container.
        
        Args:
            sandbox: Sandbox instance
            command: Command to run
            env: Optional environment variables
            
        Returns:
            Path to bundle directory
        """
        agent_id = sandbox.agent_id
        profile = sandbox.profile
        
        # Create bundle directory
        bundle_path = self.base_dir / "bundles" / agent_id
        bundle_path.mkdir(parents=True, exist_ok=True)
        
        # Create rootfs
        rootfs_path = bundle_path / "rootfs"
        rootfs_path.mkdir(exist_ok=True)
        
        # Create minimal rootfs structure
        for dir_name in ["bin", "lib", "usr", "tmp", "proc", "sys", "dev"]:
            (rootfs_path / dir_name).mkdir(exist_ok=True)
        
        # Create working directory in rootfs
        working_dir = profile.working_dir.format(agent_id=agent_id)
        working_dir_rel = working_dir.lstrip("/")
        (rootfs_path / working_dir_rel).mkdir(parents=True, exist_ok=True)
        
        # Create OCI config.json
        oci_config = {
            "ociVersion": "1.0.0",
            "process": {
                "terminal": False,
                "user": {"uid": 0, "gid": 0},
                "args": command,
                "env": [
                    f"{k}={v}" for k, v in (env or {}).items()
                ] + [
                    "PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
                    "HOME=/root",
                    "TERM=xterm"
                ],
                "cwd": working_dir,
            },
            "root": {
                "path": "rootfs",
                "readonly": False
            },
            "mounts": [
                {
                    "destination": dir_access.sandbox_path.format(agent_id=agent_id),
                    "type": "bind",
                    "source": dir_access.host_path.format(agent_id=agent_id),
                    "options": ["rbind"] + (["ro"] if dir_access.read_only else ["rw"])
                }
                for dir_access in profile.allowed_dirs
            ],
            "linux": {
                "namespaces": [
                    {"type": "pid"},
                    {"type": "network"} if profile.network_access else {"type": "network", "path": ""},
                    {"type": "ipc"},
                    {"type": "uts"},
                    {"type": "mount"}
                ],
                "resources": {
                    "devices": []
                }
            }
        }
        
        # Write config.json
        config_path = bundle_path / "config.json"
        with open(config_path, "w") as f:
            json.dump(oci_config, f, indent=2)
        
        sandbox.bundle_path = str(bundle_path)
        return str(bundle_path)
    
    def launch_in_sandbox(
        self,
        sandbox: GVisorSandbox,
        command: List[str],
        env: Optional[Dict[str, str]] = None
    ) -> subprocess.Popen:
        """
        Launch command in gVisor sandbox.
        
        Args:
            sandbox: Sandbox instance
            command: Command to run
            env: Optional environment variables
            
        Returns:
            Process handle for runsc
        """
        # Create OCI bundle
        bundle_path = self._create_oci_bundle(sandbox, command, env)
        
        container_id = sandbox.container_id
        
        # Create container: runsc create
        create_cmd = [
            self.runsc_path,
            "create",
            "--bundle", bundle_path,
            "--platform", self.platform,
            container_id
        ]
        
        create_result = subprocess.run(
            create_cmd,
            capture_output=True,
            text=True,
            timeout=30
        )
        
        if create_result.returncode != 0:
            raise RuntimeError(
                f"Failed to create gVisor container: {create_result.stderr}"
            )
        
        # Start container: runsc start
        start_cmd = [
            self.runsc_path,
            "start",
            container_id
        ]
        
        start_result = subprocess.run(
            start_cmd,
            capture_output=True,
            text=True,
            timeout=30
        )
        
        if start_result.returncode != 0:
            # Cleanup on failure
            self._cleanup_container(container_id)
            raise RuntimeError(
                f"Failed to start gVisor container: {start_result.stderr}"
            )
        
        # Execute command in container: runsc exec
        exec_cmd = [
            self.runsc_path,
            "exec",
            container_id
        ] + command
        
        # Launch process
        process = subprocess.Popen(
            exec_cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            env=env or os.environ.copy()
        )
        
        sandbox.process = process
        return process
    
    def _cleanup_container(self, container_id: str) -> None:
        """Cleanup gVisor container"""
        # Kill container
        try:
            subprocess.run(
                [self.runsc_path, "kill", container_id, "KILL"],
                capture_output=True,
                timeout=5
            )
        except Exception:
            pass
        
        # Delete container
        try:
            subprocess.run(
                [self.runsc_path, "delete", container_id],
                capture_output=True,
                timeout=5
            )
        except Exception:
            pass
    
    def destroy_sandbox(self, sandbox: GVisorSandbox) -> None:
        """
        Destroy gVisor sandbox and cleanup.
        
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
        
        # Cleanup container
        if sandbox.container_id:
            self._cleanup_container(sandbox.container_id)
        
        # Cleanup bundle (optional - may want to keep for debugging)
        # if sandbox.bundle_path:
        #     shutil.rmtree(sandbox.bundle_path, ignore_errors=True)
