// TypeScript type definitions for C++ → React bridge

// WASM module interface
export interface WASMModule {
  registerCppComponent: (name: string, factory: ComponentFactory) => void;
  createCppComponent: (name: string, props: ReactProps) => ReactElement;
  createElement: (type: string, props: ReactProps, children: ReactElement[]) => ReactElement;
  createTextElement: (text: string) => ReactElement;
  _malloc: (size: number) => number;
  _free: (ptr: number) => void;
  HEAP8: Int8Array;
  HEAP16: Int16Array;
  HEAP32: Int32Array;
  HEAPU8: Uint8Array;
  HEAPU16: Uint16Array;
  HEAPU32: Uint32Array;
  HEAPF32: Float32Array;
  HEAPF64: Float64Array;
}

// React props from C++
export interface ReactProps {
  className?: string;
  attributes?: Record<string, string | number | boolean | (() => void)>;
  children?: string[];
  // Dynamic props from C++ components - typed as unknown and validated at runtime
  [key: string]: string | number | boolean | (() => void) | string[] | undefined | unknown;
}

// React element from WASM
export interface ReactElement {
  type: string;
  props: ReactProps;
  children: ReactElement[];
}

// Component factory type
export type ComponentFactory = (props: ReactProps) => ReactElement;

// Component registry entry
export interface ComponentRegistryEntry {
  name: string;
  factory: ComponentFactory;
  component?: React.ComponentType<ReactProps>;
}

// WASM initialization options
export interface WASMInitOptions {
  locateFile?: (path: string) => string;
  onRuntimeInitialized?: () => void;
  wasmMemory?: WebAssembly.Memory;
  [key: string]: any;
}

// Component props base interface
export interface CppComponentProps {
  className?: string;
  children?: React.ReactNode;
  // Dynamic props from C++ components - typed as unknown and validated at runtime
  [key: string]: string | number | boolean | React.ReactNode | (() => void) | undefined | unknown;
}

// Error types
export class WASMLoadError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'WASMLoadError';
  }
}

export class ComponentNotFoundError extends Error {
  constructor(componentName: string) {
    super(`Component not found: ${componentName}`);
    this.name = 'ComponentNotFoundError';
  }
}

export class ComponentRegistrationError extends Error {
  constructor(message: string) {
    super(`Component registration failed: ${message}`);
    this.name = 'ComponentRegistrationError';
  }
}
