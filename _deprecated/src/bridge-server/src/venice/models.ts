/**
 * Venice Model Management
 * List models, get pricing, compare capabilities
 */
import { VeniceClient } from './client.js';

export interface Model {
  id: string;
  object: 'model';
  created: number;
  owned_by: string;
  pricing: {
    input: number; // $ per 1M tokens
    output: number; // $ per 1M tokens
  };
  tier: 'XS' | 'S' | 'M' | 'L';
  context_length: number;
}

export interface ModelsResponse {
  object: 'list';
  data: Model[];
}

/**
 * Get list of available models
 */
export async function listModels(client: VeniceClient): Promise<Model[]> {
  return client.listModels();
}

/**
 * Calculate cost for usage
 */
export function calculateCost(
  usage: { promptTokens: number; completionTokens: number },
  model: Model
): number {
  const inputCost = (usage.promptTokens / 1_000_000) * model.pricing.input;
  const outputCost = (usage.completionTokens / 1_000_000) * model.pricing.output;
  return inputCost + outputCost;
}
