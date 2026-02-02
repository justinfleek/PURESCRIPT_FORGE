/**
 * Lean LSP MCP Client
 * Connects to Lean4 LSP via Model Context Protocol
 * 
 * Re-exports complete implementation
 */
export {
  LeanMCPClient,
  type LeanGoal,
  type LeanDiagnostic,
  type LeanCompletion,
} from './mcp-client-complete.js';
