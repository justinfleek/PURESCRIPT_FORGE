// Forge.Session.Instruction FFI - Session instructions

import { randomUUID } from 'crypto';

// In-memory instruction store
const instructionStore = new Map();

// Load instructions for a session
export const loadInstructionsFFI = (sessionId) => async () => {
  const instructions = instructionStore.get(sessionId) || [];
  
  // Add default system instructions if none exist
  if (instructions.length === 0) {
    return [
      {
        id: 'system-core',
        content: 'You are a helpful AI coding assistant.',
        priority: 0,
        source: { tag: 'SystemSource' },
        enabled: true,
        tags: ['core']
      }
    ];
  }
  
  return instructions;
};

// Save an instruction
export const saveInstructionFFI = (sessionId) => (instruction) => async () => {
  try {
    let instructions = instructionStore.get(sessionId) || [];
    
    // Update existing or add new
    const existingIdx = instructions.findIndex(i => i.id === instruction.id);
    if (existingIdx >= 0) {
      instructions[existingIdx] = instruction;
    } else {
      instructions.push(instruction);
    }
    
    instructionStore.set(sessionId, instructions);
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Delete an instruction
export const deleteInstructionFFI = (sessionId) => (instructionId) => async () => {
  try {
    let instructions = instructionStore.get(sessionId) || [];
    instructions = instructions.filter(i => i.id !== instructionId);
    instructionStore.set(sessionId, instructions);
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Generate unique ID
export const generateIdFFI = async () => {
  return randomUUID();
};
