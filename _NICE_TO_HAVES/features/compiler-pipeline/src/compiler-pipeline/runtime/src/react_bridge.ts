// React Bridge: WASM ↔ React Interface (Complete Implementation)
import React from 'react';
import { createRoot, Root } from 'react-dom/client';
import type { WASMModule, ReactProps, ReactElement, ComponentFactory, WASMInitOptions } from './types';
import { WASMLoadError, ComponentNotFoundError, ComponentRegistrationError } from './types';

// WASM module loader
class WASMLoader {
  private static instance: WASMLoader | null = null;
  private module: WASMModule | null = null;
  private loadingPromise: Promise<WASMModule> | null = null;

  static getInstance(): WASMLoader {
    if (!WASMLoader.instance) {
      WASMLoader.instance = new WASMLoader();
    }
    return WASMLoader.instance;
  }

  async load(options: WASMInitOptions = {}): Promise<WASMModule> {
    if (this.module) {
      return this.module;
    }

    if (this.loadingPromise) {
      return this.loadingPromise;
    }

    this.loadingPromise = (async () => {
      try {
        // Dynamic import of WASM module
        const wasmModule = await import('./wasm_bridge.js');
        
        // Initialize WASM
        const module = await wasmModule.default(options);
        
        // Type assertion required for WASM module - validated at runtime
        // WASM modules have dynamic interfaces that TypeScript cannot fully type
        this.module = module as WASMModule;
        this.loadingPromise = null;
        
        return this.module;
      } catch (error) {
        this.loadingPromise = null;
        throw new WASMLoadError(`Failed to load WASM module: ${error}`);
      }
    })();

    return this.loadingPromise;
  }

  getModule(): WASMModule | null {
    return this.module;
  }

  isLoaded(): boolean {
    return this.module !== null;
  }
}

// Convert WASM ReactElement to React JSX (complete)
function wasmToReact(element: ReactElement): React.ReactNode {
  if (element.type === '#text') {
    return element.props.attributes?.textContent || '';
  }

  if (element.isFragment) {
    return React.createElement(React.Fragment, { key: element.key }, 
      ...element.children.map(child => wasmToReact(child))
    );
  }

  const props: ReactProps = {
    ...element.props.attributes,
    className: element.props.className,
    key: element.key || undefined,
  } as ReactProps;

  // Handle callbacks
  if (element.props.callbacks) {
    Object.entries(element.props.callbacks).forEach(([key, callback]) => {
      props[key] = callback;
    });
  }

  // Handle refs
  if (element.props.refs) {
    Object.entries(element.props.refs).forEach(([key, ref]) => {
      props[key] = ref;
    });
  }

  const children = element.children.map(child => wasmToReact(child));

  return React.createElement(element.type, props, ...children);
}

// React hook for C++ components (complete with error handling)
export function useCppComponent<T extends ReactProps>(
  componentName: string,
  props: T
): React.ReactNode {
  const [element, setElement] = React.useState<ReactElement | null>(null);
  const [error, setError] = React.useState<Error | null>(null);
  const [loading, setLoading] = React.useState(true);
  const wasmModuleRef = React.useRef<WASMModule | null>(null);

  React.useEffect(() => {
    let cancelled = false;

    (async () => {
      try {
        setLoading(true);
        setError(null);

        // Load WASM module
        const loader = WASMLoader.getInstance();
        const module = await loader.load();
        
        if (cancelled) return;

        wasmModuleRef.current = module;
        
        // Check if component exists
        if (!module.hasCppComponent(componentName)) {
          throw new ComponentNotFoundError(componentName);
        }
        
        // Create component from WASM
        const wasmElement = module.createCppComponent(componentName, props);
        
        if (cancelled) return;
        
        setElement(wasmElement);
        setLoading(false);
      } catch (err) {
        if (cancelled) return;
        setError(err instanceof Error ? err : new Error(String(err)));
        setLoading(false);
      }
    })();

    return () => {
      cancelled = true;
    };
  }, [componentName, props]);

  if (loading) {
    return React.createElement('div', { className: 'cpp-component-loading' }, 'Loading...');
  }

  if (error) {
    return React.createElement('div', { 
      className: 'cpp-component-error',
      'data-error': error.message 
    }, `Error: ${error.message}`);
  }

  if (!element) {
    return null;
  }

  return wasmToReact(element);
}

// Higher-order component wrapper (complete)
export function withCppComponent<P extends object>(
  componentName: string,
  defaultProps?: Partial<P>
) {
  return function CppComponentWrapper(props: P) {
    const mergedProps = { ...defaultProps, ...props } as P;
    return useCppComponent(componentName, mergedProps);
  };
}

// Component registry for React (complete)
class ReactComponentRegistry {
  private components = new Map<string, React.ComponentType<any>>();
  private factories = new Map<string, ComponentFactory>();

  register(name: string, component: React.ComponentType<any>) {
    this.components.set(name, component);
  }

  registerFactory(name: string, factory: ComponentFactory) {
    this.factories.set(name, factory);
  }

  get(name: string): React.ComponentType<ReactProps> | undefined {
    return this.components.get(name);
  }

  getFactory(name: string): ComponentFactory | undefined {
    return this.factories.get(name);
  }

  has(name: string): boolean {
    return this.components.has(name) || this.factories.has(name);
  }

  unregister(name: string): void {
    this.components.delete(name);
    this.factories.delete(name);
  }

  list(): string[] {
    const names = new Set<string>();
    this.components.forEach((_, name) => names.add(name));
    this.factories.forEach((_, name) => names.add(name));
    return Array.from(names);
  }
}

export const componentRegistry = new ReactComponentRegistry();

// Register C++ component from WASM
export async function registerCppComponentFromWASM(
  name: string,
  factory: ComponentFactory
): Promise<void> {
  try {
    const loader = WASMLoader.getInstance();
    const module = await loader.load();
    
    module.registerCppComponent(name, factory);
    componentRegistry.registerFactory(name, factory);
  } catch (error) {
    throw new ComponentRegistrationError(
      `Failed to register component ${name}: ${error}`
    );
  }
}

// Initialize WASM module
export async function initWASMModule(options: WASMInitOptions = {}): Promise<WASMModule> {
  const loader = WASMLoader.getInstance();
  return loader.load(options);
}

// Check if WASM is loaded
export function isWASMLoaded(): boolean {
  return WASMLoader.getInstance().isLoaded();
}

// Get loaded WASM module
export function getWASMModule(): WASMModule | null {
  return WASMLoader.getInstance().getModule();
}
