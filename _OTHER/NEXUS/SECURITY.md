# Nexus Security Architecture
## Bubblewrap Sandboxing for Agent Isolation

---

## 🔒 Security Principle

**All Nexus agents MUST run in bubblewrap sandboxes** with restricted folder access. Agents can only access:
- Their designated working directory
- Shared read-only directories (if needed)
- Network access (for web search agents only)
- No access to system directories
- No access to other agents' directories

---

## 🛡️ Bubblewrap Integration

### What is Bubblewrap?

Bubblewrap (`bwrap`) is a Linux sandboxing tool that uses Linux namespaces to create isolated environments. It's used by Flatpak, systemd, and other containerized applications.

**Key Features:**
- **Namespace isolation** - Process, mount, network namespaces
- **Read-only bind mounts** - Share directories read-only
- **Read-write bind mounts** - Allow write access to specific directories
- **Network access control** - Allow/deny network access
- **User/group isolation** - Run as unprivileged user

---

## 📁 Sandbox Configuration

### Agent Sandbox Profiles

Each agent type has a **sandbox profile** defining:
- **Allowed directories** (read-only or read-write)
- **Network access** (allowed or denied)
- **Working directory** (agent's private directory)
- **Shared directories** (read-only access to shared data)

---

### 1. Web Search Agent Sandbox

**Purpose:** Search the web, fetch content

**Allowed Access:**
- ✅ `/tmp/nexus/agents/{agent_id}/` - Read-write (working directory)
- ✅ `/tmp/nexus/shared/content/` - Read-write (store fetched content)
- ✅ `/tmp/nexus/shared/semantic-memory/` - Read-only (query semantic cells)
- ✅ Network access - Allowed (for web search)

**Denied Access:**
- ❌ System directories (`/usr`, `/etc`, `/home`, etc.)
- ❌ Other agents' directories
- ❌ Database files (direct access)
- ❌ Network graph files (direct access)

**Bubblewrap Command:**
```bash
bwrap \
  --ro-bind /tmp/nexus/shared/semantic-memory /tmp/nexus/shared/semantic-memory \
  --bind /tmp/nexus/agents/{agent_id} /tmp/nexus/agents/{agent_id} \
  --bind /tmp/nexus/shared/content /tmp/nexus/shared/content \
  --unshare-net \
  --unshare-ipc \
  --unshare-pid \
  --unshare-uts \
  --die-with-parent \
  --new-session \
  python3 web_search_agent.py
```

---

### 2. Content Extraction Agent Sandbox

**Purpose:** Extract entities, relations, concepts from content

**Allowed Access:**
- ✅ `/tmp/nexus/agents/{agent_id}/` - Read-write (working directory)
- ✅ `/tmp/nexus/shared/content/` - Read-only (read fetched content)
- ✅ `/tmp/nexus/shared/semantic-memory/` - Read-write (store extracted entities)
- ❌ Network access - Denied (no network needed)

**Denied Access:**
- ❌ System directories
- ❌ Other agents' directories
- ❌ Database files (direct access)
- ❌ Network graph files (direct access)

**Bubblewrap Command:**
```bash
bwrap \
  --ro-bind /tmp/nexus/shared/content /tmp/nexus/shared/content \
  --bind /tmp/nexus/shared/semantic-memory /tmp/nexus/shared/semantic-memory \
  --bind /tmp/nexus/agents/{agent_id} /tmp/nexus/agents/{agent_id} \
  --unshare-net \
  --unshare-ipc \
  --unshare-pid \
  --unshare-uts \
  --die-with-parent \
  --new-session \
  python3 content_extraction_agent.py
```

---

### 3. Network Formation Agent Sandbox

**Purpose:** Form social networks from discovered content

**Allowed Access:**
- ✅ `/tmp/nexus/agents/{agent_id}/` - Read-write (working directory)
- ✅ `/tmp/nexus/shared/semantic-memory/` - Read-only (read entities/relations)
- ✅ `/tmp/nexus/shared/network-graph/` - Read-write (update network graph)
- ❌ Network access - Denied (no network needed)

**Denied Access:**
- ❌ System directories
- ❌ Other agents' directories
- ❌ Content files (direct access)
- ❌ Database files (direct access)

**Bubblewrap Command:**
```bash
bwrap \
  --ro-bind /tmp/nexus/shared/semantic-memory /tmp/nexus/shared/semantic-memory \
  --bind /tmp/nexus/shared/network-graph /tmp/nexus/shared/network-graph \
  --bind /tmp/nexus/agents/{agent_id} /tmp/nexus/agents/{agent_id} \
  --unshare-net \
  --unshare-ipc \
  --unshare-pid \
  --unshare-uts \
  --die-with-parent \
  --new-session \
  python3 network_formation_agent.py
```

---

### 4. Database Layer Sandbox

**Purpose:** Persist agent data, semantic memory, network graphs

**Allowed Access:**
- ✅ `/tmp/nexus/database/` - Read-write (database files)
- ✅ `/tmp/nexus/shared/semantic-memory/` - Read-write (semantic cells)
- ✅ `/tmp/nexus/shared/network-graph/` - Read-write (network graphs)
- ✅ `/tmp/nexus/shared/content/` - Read-write (content storage)
- ❌ Network access - Denied (no network needed)

**Denied Access:**
- ❌ System directories
- ❌ Agent directories (direct access)
- ❌ Other database files

**Bubblewrap Command:**
```bash
bwrap \
  --bind /tmp/nexus/database /tmp/nexus/database \
  --bind /tmp/nexus/shared/semantic-memory /tmp/nexus/shared/semantic-memory \
  --bind /tmp/nexus/shared/network-graph /tmp/nexus/shared/network-graph \
  --bind /tmp/nexus/shared/content /tmp/nexus/shared/content \
  --unshare-net \
  --unshare-ipc \
  --unshare-pid \
  --unshare-uts \
  --die-with-parent \
  --new-session \
  python3 database_layer.py
```

---

## 🏗️ Directory Structure

```
/tmp/nexus/
├── agents/                      # Agent working directories
│   ├── {agent_id_1}/           # Web Search Agent 1
│   │   └── (agent private files)
│   ├── {agent_id_2}/           # Content Extraction Agent 1
│   │   └── (agent private files)
│   └── {agent_id_3}/           # Network Formation Agent 1
│       └── (agent private files)
│
├── shared/                      # Shared directories (read-only or read-write)
│   ├── semantic-memory/         # Semantic cells, couplings
│   ├── network-graph/           # Network graph files
│   └── content/                 # Web content cache
│
└── database/                    # Database files (SQLite, DuckDB)
    ├── agents.db                # Agent configurations/states
    ├── semantic.db              # Semantic cells/couplings
    ├── network.db               # Network graphs
    └── content.db               # Content storage
```

---

## 🔧 Implementation

### Sandbox Manager Module

**File:** `NEXUS/agent-orchestrator/src/sandbox_manager.py`

**Purpose:** Create and manage bubblewrap sandboxes for agents

**Interface:**
```python
class SandboxManager:
    def create_sandbox(self, agent_type: AgentType, agent_id: str, config: SandboxConfig) -> Sandbox
    def launch_in_sandbox(self, sandbox: Sandbox, command: List[str]) -> subprocess.Popen
    def destroy_sandbox(self, sandbox: Sandbox) -> None
    def get_sandbox_profile(self, agent_type: AgentType) -> SandboxProfile
```

**Sandbox Profiles:**
```python
@dataclass
class SandboxProfile:
    agent_type: AgentType
    allowed_dirs: List[DirectoryAccess]  # (path, read_only)
    network_access: bool
    working_dir: str
    shared_dirs: List[DirectoryAccess]
```

**Directory Access:**
```python
@dataclass
class DirectoryAccess:
    host_path: str
    sandbox_path: str
    read_only: bool
```

---

### Agent Orchestrator Integration

**File:** `NEXUS/agent-orchestrator/src/launcher.py`

**Modified Interface:**
```python
class AgentLauncher:
    def launch_agent(
        self,
        agent_type: AgentType,
        config: AgentConfig,
        sandbox_config: Optional[SandboxConfig] = None
    ) -> AgentID:
        # Create sandbox
        sandbox = sandbox_manager.create_sandbox(agent_type, agent_id, sandbox_config)
        
        # Launch agent in sandbox
        process = sandbox_manager.launch_in_sandbox(sandbox, agent_command)
        
        return agent_id
```

---

## 🧪 Testing Sandbox Security

### Test 1: Directory Access
```python
def test_web_search_agent_cannot_access_system_dirs():
    agent = launch_agent(WebSearchAgent, sandbox_config)
    # Try to access /etc/passwd
    result = agent.execute("cat /etc/passwd")
    assert result.exit_code != 0  # Should fail
```

### Test 2: Network Access
```python
def test_content_extraction_agent_no_network():
    agent = launch_agent(ContentExtractionAgent, sandbox_config)
    # Try to connect to internet
    result = agent.execute("curl https://example.com")
    assert result.exit_code != 0  # Should fail
```

### Test 3: Cross-Agent Isolation
```python
def test_agents_cannot_access_each_other():
    agent1 = launch_agent(WebSearchAgent, sandbox_config)
    agent2 = launch_agent(ContentExtractionAgent, sandbox_config)
    # Agent1 tries to access agent2's directory
    result = agent1.execute(f"ls /tmp/nexus/agents/{agent2.id}")
    assert result.exit_code != 0  # Should fail
```

---

## 📋 Sandbox Configuration Files

### Web Search Agent Profile

**File:** `NEXUS/agent-orchestrator/profiles/web_search_agent.json`

```json
{
  "agent_type": "web_search",
  "allowed_dirs": [
    {
      "host_path": "/tmp/nexus/agents/{agent_id}",
      "sandbox_path": "/tmp/nexus/agents/{agent_id}",
      "read_only": false
    },
    {
      "host_path": "/tmp/nexus/shared/content",
      "sandbox_path": "/tmp/nexus/shared/content",
      "read_only": false
    },
    {
      "host_path": "/tmp/nexus/shared/semantic-memory",
      "sandbox_path": "/tmp/nexus/shared/semantic-memory",
      "read_only": true
    }
  ],
  "network_access": true,
  "working_dir": "/tmp/nexus/agents/{agent_id}",
  "shared_dirs": [
    "/tmp/nexus/shared/content",
    "/tmp/nexus/shared/semantic-memory"
  ]
}
```

---

## 🔐 Security Best Practices

### 1. Principle of Least Privilege
- Each agent gets **minimum required access**
- Read-only access when possible
- No access to system directories

### 2. Namespace Isolation
- **Process namespace** - Agents can't see other processes
- **Mount namespace** - Agents can't see system mounts
- **Network namespace** - Agents can't access network (unless needed)
- **IPC namespace** - Agents can't use shared memory
- **UTS namespace** - Agents can't change hostname

### 3. Directory Permissions
- Agent directories: `700` (owner read/write/execute only)
- Shared directories: `755` (owner read/write/execute, others read/execute)
- Database directories: `700` (owner only)

### 4. User Isolation
- Run agents as **unprivileged user** (`nexus-agent`)
- Use `--unshare-user` for user namespace isolation
- Drop capabilities with `--cap-drop ALL`

---

## 🚀 Implementation Plan

### Phase 1: Sandbox Infrastructure (Week 1)
1. ✅ **Sandbox Manager** - Create/manage bubblewrap sandboxes
2. ✅ **Sandbox Profiles** - Define profiles for each agent type
3. ✅ **Directory Setup** - Create directory structure with correct permissions

### Phase 2: Agent Integration (Week 2)
4. ✅ **Agent Launcher** - Launch agents in sandboxes
5. ✅ **Sandbox Testing** - Test sandbox security
6. ✅ **Error Handling** - Handle sandbox failures

### Phase 3: Security Hardening (Week 3)
7. ✅ **Security Tests** - Test directory access, network access, isolation
8. ✅ **Audit Logging** - Log sandbox violations
9. ✅ **Monitoring** - Monitor sandbox health

---

## 📊 Sandbox Profile Summary

| Agent Type | Network | Read-Only Dirs | Read-Write Dirs |
|------------|---------|----------------|-----------------|
| **Web Search** | ✅ Yes | semantic-memory | agent dir, content |
| **Content Extraction** | ❌ No | content | agent dir, semantic-memory |
| **Network Formation** | ❌ No | semantic-memory | agent dir, network-graph |
| **Database Layer** | ❌ No | - | database, semantic-memory, network-graph, content |
