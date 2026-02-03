// Registry.js - FFI for MessagePart Registry
// Tool and part component registration

// Module state
const toolRegistry = new Map();
const partRegistry = new Map();

// Register a tool renderer
export const registerTool = (input) => () => {
  toolRegistry.set(input.name, input);
};

// Get a registered tool renderer
export const getTool = (name) => () => {
  const entry = toolRegistry.get(name);
  if (!entry || !entry.render) return null;
  
  // Handle Maybe wrapper
  const render = entry.render?.value0 ?? entry.render?.value ?? entry.render;
  return render ? { value0: render } : null;
};

// Split path into parts
export const splitPath = (path) => {
  if (!path) return [];
  return path.split(/[/\\]/);
};

// Get last element of array
export const lastElement = (arr) => {
  if (!arr || arr.length === 0) return "";
  return arr[arr.length - 1];
};

// Register a part component for a type
export const registerPartComponent = (partType) => (component) => () => {
  partRegistry.set(partType, component);
};

// Get a registered part component
export const getPartComponent = (partType) => () => {
  const component = partRegistry.get(partType);
  return component ? { value0: component } : null;
};
