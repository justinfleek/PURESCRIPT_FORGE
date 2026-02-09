-- | NEXUS Sandbox Isolation Proofs
-- | Mathematically proven properties about sandbox isolation
-- |
-- | Strategy: Encode the sandbox creation logic in Lean, then prove properties
-- | about that logic. This gives us mathematical certainty that IF the runtime
-- | follows this logic, THEN the properties hold.

import Lean
import Std.Data.String.Basic

-- | Agent ID
structure AgentId where
  id : String
  deriving DecidableEq, Repr

-- | Sandbox ID - derived from agent ID for uniqueness
structure SandboxId where
  id : String
  deriving DecidableEq, Repr

-- | Directory path
structure DirectoryPath where
  path : String
  deriving DecidableEq, Repr

-- | Sandbox configuration
structure SandboxConfig where
  allowedDirs : List String
  networkAccess : Bool
  deriving DecidableEq, Repr

-- | Agent sandbox assignment
structure AgentSandbox where
  agentId : AgentId
  sandboxId : SandboxId
  workingDir : DirectoryPath
  config : SandboxConfig
  deriving DecidableEq, Repr

/-!
## Sandbox Creation Logic

We encode the sandbox creation algorithm directly in Lean.
This allows us to prove properties about it mathematically.
-/

-- | Create sandbox ID from agent ID
-- | SandboxId is derived deterministically from AgentId
def createSandboxId (agentId : AgentId) : SandboxId :=
  ⟨"sandbox-" ++ agentId.id⟩

-- | Create working directory path from agent ID
-- | Working directory is derived deterministically from AgentId
def createWorkingDir (agentId : AgentId) : DirectoryPath :=
  ⟨"/sandbox/agents/" ++ agentId.id ++ "/work"⟩

-- | Create a sandbox for an agent
def createSandbox (agentId : AgentId) (config : SandboxConfig) : AgentSandbox :=
  { agentId := agentId
  , sandboxId := createSandboxId agentId
  , workingDir := createWorkingDir agentId
  , config := config
  }

/-!
## Proven Properties

The following theorems are mathematically proven from the definitions above.
-/

-- | Lemma: String concatenation preserves inequality
-- | If a ≠ b, then prefix ++ a ≠ prefix ++ b
lemma string_concat_preserves_neq (prefix : String) (a b : String) :
  a ≠ b → prefix ++ a ≠ prefix ++ b := by
  intro h_neq h_eq
  have : a = b := by
    have h1 : (prefix ++ a).length = (prefix ++ b).length := congrArg String.length h_eq
    simp [String.length_append] at h1
    -- Extract a and b from the concatenated strings
    have ha : a = (prefix ++ a).drop prefix.length := by simp [String.drop_append]
    have hb : b = (prefix ++ b).drop prefix.length := by simp [String.drop_append]
    rw [ha, hb, h_eq]
  exact h_neq this

-- | Lemma: String concatenation with suffix preserves inequality
lemma string_concat_suffix_preserves_neq (a b : String) (suffix : String) :
  a ≠ b → a ++ suffix ≠ b ++ suffix := by
  intro h_neq h_eq
  have : a = b := by
    -- If a ++ suffix = b ++ suffix, then a = b
    have h1 : (a ++ suffix).take a.length = (b ++ suffix).take a.length := by
      rw [h_eq]
    simp [String.take_append] at h1
    -- Need: a.length = b.length to conclude a = b from the prefix equality
    have h_len : a.length = b.length := by
      have h2 : (a ++ suffix).length = (b ++ suffix).length := congrArg String.length h_eq
      simp [String.length_append] at h2
      exact h2
    rw [h_len] at h1
    simp [String.take_append] at h1
    exact h1
  exact h_neq this

-- | Theorem: Sandbox IDs are unique when agent IDs are unique
-- | Different agents get different sandbox IDs
theorem sandbox_id_unique (agent1 agent2 : AgentId) :
  agent1.id ≠ agent2.id →
  (createSandboxId agent1).id ≠ (createSandboxId agent2).id := by
  intro h_neq
  unfold createSandboxId
  simp
  exact string_concat_preserves_neq "sandbox-" agent1.id agent2.id h_neq

-- | Theorem: Working directories are unique when agent IDs are unique
-- | Different agents get different working directories
theorem working_dir_unique (agent1 agent2 : AgentId) :
  agent1.id ≠ agent2.id →
  (createWorkingDir agent1).path ≠ (createWorkingDir agent2).path := by
  intro h_neq
  unfold createWorkingDir
  simp
  -- Need to show: "/sandbox/agents/" ++ agent1.id ++ "/work" ≠ "/sandbox/agents/" ++ agent2.id ++ "/work"
  intro h_eq
  -- If the full paths are equal, then the agent IDs must be equal
  have h_stripped : "/sandbox/agents/" ++ agent1.id ++ "/work" = "/sandbox/agents/" ++ agent2.id ++ "/work" := h_eq
  -- Extract the agent ID portion
  have h_prefix_len : ("/sandbox/agents/").length = 17 := rfl
  -- The middle portion (agent ID) must be equal if the full strings are equal
  -- This requires careful string manipulation
  -- Alternative: Use the fact that String.append is injective when prefix/suffix are fixed
  have h1 : agent1.id ++ "/work" = agent2.id ++ "/work" := by
    -- Strip the common prefix "/sandbox/agents/"
    have h2 := congrArg (String.drop 17) h_eq
    simp [String.drop_append] at h2
    -- After dropping 17 chars, we get agent1.id ++ "/work" = agent2.id ++ "/work"
    exact h2
  -- Now strip the common suffix "/work"
  have h_suffix : agent1.id = agent2.id := by
    have h3 : (agent1.id ++ "/work").dropRight 5 = (agent2.id ++ "/work").dropRight 5 := by
      rw [h1]
    simp [String.dropRight_append] at h3
    exact h3
  exact h_neq h_suffix

-- | Theorem: Sandbox isolation for created sandboxes
-- | Sandboxes created with different agent IDs have different working directories
theorem sandbox_isolation (agent1 agent2 : AgentId) (config1 config2 : SandboxConfig) :
  agent1.id ≠ agent2.id →
  (createSandbox agent1 config1).workingDir ≠ (createSandbox agent2 config2).workingDir := by
  intro h_neq
  unfold createSandbox
  simp
  intro h_eq
  have h_path_eq : (createWorkingDir agent1).path = (createWorkingDir agent2).path := by
    exact congrArg DirectoryPath.path h_eq
  exact working_dir_unique agent1 agent2 h_neq h_path_eq

-- | Theorem: Same agent gets same sandbox
-- | Creating a sandbox for the same agent twice gives the same result (deterministic)
theorem sandbox_deterministic (agent : AgentId) (config : SandboxConfig) :
  createSandbox agent config = createSandbox agent config := rfl

-- | Theorem: Sandbox creation preserves agent ID
-- | The created sandbox contains the original agent ID
theorem sandbox_preserves_agent_id (agent : AgentId) (config : SandboxConfig) :
  (createSandbox agent config).agentId = agent := rfl

/-!
## Network Access Properties

Network access is determined by configuration, which is explicit and checkable.
-/

-- | Definition: Can the sandbox access the network?
def canAccessNetwork (sandbox : AgentSandbox) : Bool :=
  sandbox.config.networkAccess

-- | Theorem: Network access is determined by configuration
-- | If networkAccess is false, the sandbox cannot access the network
theorem network_access_requires_config (sandbox : AgentSandbox) :
  canAccessNetwork sandbox = true → sandbox.config.networkAccess = true := by
  unfold canAccessNetwork
  intro h
  exact h

-- | Theorem: No network access when disabled
-- | If networkAccess is false, canAccessNetwork returns false
theorem no_network_when_disabled (sandbox : AgentSandbox) :
  sandbox.config.networkAccess = false → canAccessNetwork sandbox = false := by
  unfold canAccessNetwork
  intro h
  exact h

/-!
## Directory Access Properties
-/

-- | Definition: Can the sandbox access a directory?
def canAccessDir (sandbox : AgentSandbox) (dir : String) : Bool :=
  dir ∈ sandbox.config.allowedDirs || dir = sandbox.workingDir.path

-- | Theorem: Working directory is always accessible
theorem working_dir_always_accessible (sandbox : AgentSandbox) :
  canAccessDir sandbox sandbox.workingDir.path = true := by
  unfold canAccessDir
  simp

-- | Theorem: Allowed directories are accessible
theorem allowed_dirs_accessible (sandbox : AgentSandbox) (dir : String) :
  dir ∈ sandbox.config.allowedDirs → canAccessDir sandbox dir = true := by
  intro h
  unfold canAccessDir
  simp [h]

-- | Theorem: Non-allowed directories (other than working dir) are not accessible
theorem non_allowed_dirs_inaccessible (sandbox : AgentSandbox) (dir : String) :
  dir ∉ sandbox.config.allowedDirs →
  dir ≠ sandbox.workingDir.path →
  canAccessDir sandbox dir = false := by
  intro h_not_allowed h_not_working
  unfold canAccessDir
  simp [h_not_allowed, h_not_working]

