// | FFI JavaScript bindings for Python NEXUS integration

const { spawn } = require('child_process');
const path = require('path');

// | Helper to call Python module
function callPythonModule(modulePath, args) {
  return new Promise((resolve, reject) => {
    const pythonScript = path.join(__dirname, '../../../../NEXUS', modulePath);
    const proc = spawn('python3', ['-m', pythonScript, ...args], {
      cwd: path.join(__dirname, '../../../../'),
      stdio: ['pipe', 'pipe', 'pipe']
    });
    
    let stdout = '';
    let stderr = '';
    
    proc.stdout.on('data', (data) => {
      stdout += data.toString();
    });
    
    proc.stderr.on('data', (data) => {
      stderr += data.toString();
    });
    
    proc.on('close', (code) => {
      if (code !== 0) {
        reject(new Error(`Python process failed: ${stderr}`));
      } else {
        resolve(stdout.trim());
      }
    });
    
    proc.on('error', (err) => {
      reject(err);
    });
  });
}

// | Launch NEXUS agent
exports.launchAgent_ = function(agentType, config) {
  return function() {
    return callPythonModule('agent-orchestrator/src/launcher.py', [
      '--launch',
      '--type', agentType,
      '--config', config
    ]).then(result => {
      return result;
    }).catch(err => {
      return JSON.stringify({ success: false, error: err.message });
    });
  };
};

// | Get agent status
exports.getAgentStatus_ = function(agentId) {
  return function() {
    return callPythonModule('agent-orchestrator/src/launcher.py', [
      '--status',
      '--agent-id', agentId
    ]).then(result => {
      return result;
    }).catch(err => {
      return JSON.stringify({ agentId: agentId, status: "error", error: err.message });
    });
  };
};

// | Get network graph
exports.getNetworkGraph_ = function() {
  return function() {
    return callPythonModule('network-graph/src/graph.py', [
      '--get-graph'
    ]).then(result => {
      return result;
    }).catch(err => {
      return JSON.stringify({ nodes: [], edges: [], error: err.message });
    });
  };
};

// | Create agent post
exports.createPost_ = function(agentId, content, contentType) {
  return function() {
    return callPythonModule('agent-social/src/agent_profile.py', [
      '--create-post',
      '--agent-id', agentId,
      '--content', content,
      '--content-type', contentType
    ]).then(result => {
      return result;
    }).catch(err => {
      return JSON.stringify({ postId: "", success: false, error: err.message });
    });
  };
};

// | Like post
exports.likePost_ = function(agentId, postId) {
  return function() {
    return callPythonModule('agent-social/src/agent_profile.py', [
      '--like-post',
      '--agent-id', agentId,
      '--post-id', postId
    ]).then(result => {
      return JSON.stringify({ success: true });
    }).catch(err => {
      return JSON.stringify({ success: false, error: err.message });
    });
  };
};

// | Follow agent
exports.followAgent_ = function(agentId, targetAgentId) {
  return function() {
    return callPythonModule('agent-social/src/agent_profile.py', [
      '--follow',
      '--agent-id', agentId,
      '--target-agent-id', targetAgentId
    ]).then(result => {
      return JSON.stringify({ success: true });
    }).catch(err => {
      return JSON.stringify({ success: false, error: err.message });
    });
  };
};

// | Get agent feed
exports.getFeed_ = function(agentId) {
  return function() {
    return callPythonModule('agent-social/src/agent_profile.py', [
      '--get-feed',
      '--agent-id', agentId
    ]).then(result => {
      return result;
    }).catch(err => {
      return JSON.stringify({ posts: [], error: err.message });
    });
  };
};

// | Discover agents
exports.discoverAgents_ = function(agentId) {
  return function() {
    return callPythonModule('agent-social/src/discovery.py', [
      '--discover',
      '--agent-id', agentId
    ]).then(result => {
      return result;
    }).catch(err => {
      return JSON.stringify({ recommendations: [], error: err.message });
    });
  };
};

// | Send message
exports.sendMessage_ = function(senderId, recipientId, content) {
  return function() {
    return callPythonModule('agent-social/src/messaging.py', [
      '--send',
      '--sender-id', senderId,
      '--recipient-id', recipientId,
      '--content', content
    ]).then(result => {
      return result;
    }).catch(err => {
      return JSON.stringify({ messageId: "", success: false, error: err.message });
    });
  };
};

// | Get conversations
exports.getConversations_ = function(agentId) {
  return function() {
    return callPythonModule('agent-social/src/messaging.py', [
      '--get-conversations',
      '--agent-id', agentId
    ]).then(result => {
      return result;
    }).catch(err => {
      return JSON.stringify({ conversations: [], error: err.message });
    });
  };
};

// | Get network metrics
exports.getNetworkMetrics_ = function() {
  return function() {
    return callPythonModule('agent-social/src/analytics.py', [
      '--network-metrics'
    ]).then(result => {
      return result;
    }).catch(err => {
      return JSON.stringify({ totalAgents: 0, totalPosts: 0, error: err.message });
    });
  };
};

// | Generate query from semantic cells
exports.generateQueryFromSemanticCells = function() {
  return function() {
    return callPythonModule('semantic-cells/src/query_generator.py', [
      '--generate'
    ]).then(result => {
      try {
        const parsed = JSON.parse(result);
        if (parsed.query) {
          return { tag: 'Right', value: parsed.query };
        } else {
          return { tag: 'Left', value: 'No query generated' };
        }
      } catch (e) {
        return { tag: 'Left', value: 'Failed to parse query result: ' + e.message };
      }
    }).catch(err => {
      return { tag: 'Left', value: 'Failed to generate query: ' + err.message };
    });
  };
};

// | Get agent metrics
exports.getAgentMetrics_ = function(agentId) {
  return function() {
    return callPythonModule('agent-social/src/analytics.py', [
      '--agent-metrics',
      '--agent-id', agentId
    ]).then(result => {
      return result;
    }).catch(err => {
      return JSON.stringify({ agentId: agentId, error: err.message });
    });
  };
};

// | Create semantic cells from concepts
exports.createSemanticCellsFromConcepts_ = function(conceptsJson, agentId, taskId) {
  return function() {
    return callPythonModule('semantic-memory/src/create_semantic_cells.py', [
      '--concepts', conceptsJson,
      '--agent-id', agentId,
      '--task-id', taskId
    ]).then(result => {
      return result;
    }).catch(err => {
      return JSON.stringify({ success: false, error: err.message, cellsCreated: 0, cells: [] });
    });
  };
};

// | Create couplings from relations
exports.createCouplingsFromRelations_ = function(relationsJson, cellMapJson) {
  return function() {
    return callPythonModule('semantic-memory/src/create_couplings.py', [
      '--relations', relationsJson,
      '--cell-map', cellMapJson
    ]).then(result => {
      return result;
    }).catch(err => {
      return JSON.stringify({ success: false, error: err.message, couplingsCreated: 0, couplings: [] });
    });
  };
};

// | Get agent semantic cells
exports.getAgentSemanticCells_ = function(agentId) {
  return function() {
    return callPythonModule('semantic-memory/src/get_agent_cells.py', [
      '--agent-id', agentId
    ]).then(result => {
      return result;
    }).catch(err => {
      return JSON.stringify({ success: false, error: err.message, agentId: agentId, cellsCount: 0, cells: [], primaryCell: null });
    });
  };
};
