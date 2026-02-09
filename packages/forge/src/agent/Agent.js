// Forge.Agent.Agent FFI - Agent system

import * as fs from 'fs/promises';

// Load custom agents from config file
export const loadCustomAgentsFFI = (configPath) => async () => {
  try {
    const content = await fs.readFile(configPath, 'utf-8');
    const config = JSON.parse(content);
    
    if (!config.agents || !Array.isArray(config.agents)) {
      return [];
    }
    
    return config.agents.map(agent => ({
      id: agent.id || 'custom',
      name: agent.name || 'Custom Agent',
      description: agent.description || '',
      mode: agent.mode === 'subagent' ? { tag: 'Subagent' } : { tag: 'Primary' },
      systemPrompt: agent.systemPrompt || '',
      tools: agent.tools || [],
      maxTokens: agent.maxTokens || 8192,
      temperature: agent.temperature || 0.7
    }));
  } catch (err) {
    // Config file doesn't exist or is invalid - return empty array
    return [];
  }
};
