// Forge.ACP.Agent FFI - Agent registry

// In-memory agent registry (in production, use persistent storage)
const agentRegistry = new Map();

// Store agent in registry
export const storeAgentFFI = (config) => async () => {
  try {
    const now = Date.now();
    const agent = {
      config,
      status: { tag: 'StatusIdle' },
      registeredAt: now,
      lastActive: now
    };
    agentRegistry.set(config.id, agent);
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Remove agent from registry
export const removeAgentFFI = (agentId) => async () => {
  try {
    if (!agentRegistry.has(agentId)) {
      return { tag: 'Left', value: `Agent not found: ${agentId}` };
    }
    agentRegistry.delete(agentId);
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Get all agents from registry
export const getAllAgentsFFI = async () => {
  return Array.from(agentRegistry.values()).map(agent => ({
    config: agent.config,
    status: mapStatus(agent.status),
    registeredAt: agent.registeredAt,
    lastActive: agent.lastActive
  }));
};

// Get agent by ID
export const getAgentFFI = (agentId) => async () => {
  const agent = agentRegistry.get(agentId);
  if (!agent) {
    return null;
  }
  return {
    config: agent.config,
    status: mapStatus(agent.status),
    registeredAt: agent.registeredAt,
    lastActive: agent.lastActive
  };
};

// Update agent status
export const updateStatusFFI = (agentId) => (statusStr) => async () => {
  try {
    const agent = agentRegistry.get(agentId);
    if (!agent) {
      return { tag: 'Left', value: `Agent not found: ${agentId}` };
    }
    agent.status = parseStatus(statusStr);
    agent.lastActive = Date.now();
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Helper to map status to PureScript ADT format
function mapStatus(status) {
  if (status.tag === 'StatusIdle') return { tag: 'StatusIdle' };
  if (status.tag === 'StatusBusy') return { tag: 'StatusBusy' };
  if (status.tag === 'StatusOffline') return { tag: 'StatusOffline' };
  if (status.tag === 'StatusError') return { tag: 'StatusError', value: status.value };
  return { tag: 'StatusIdle' };
}

// Helper to parse status string
function parseStatus(str) {
  if (str === 'idle') return { tag: 'StatusIdle' };
  if (str === 'busy') return { tag: 'StatusBusy' };
  if (str === 'offline') return { tag: 'StatusOffline' };
  if (str.startsWith('error:')) return { tag: 'StatusError', value: str.slice(7) };
  return { tag: 'StatusIdle' };
}
