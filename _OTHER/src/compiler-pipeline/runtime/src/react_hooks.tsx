// React Hooks for C++ Components
import React from 'react';
import { useCppComponent } from './react_bridge';

// Hook for C++ component with state
export function useCppComponentState<T extends ReactProps>(
  componentName: string,
  initialProps: T
): [React.ReactNode, (props: Partial<T>) => void] {
  const [props, setProps] = React.useState<T>(initialProps);
  const component = useCppComponent(componentName, props);

  const updateProps = React.useCallback((newProps: Partial<T>) => {
    setProps(prev => ({ ...prev, ...newProps }));
  }, []);

  return [component, updateProps];
}

// Hook for C++ component with effects
export function useCppComponentEffect<T extends ReactProps>(
  componentName: string,
  props: T,
  deps: React.DependencyList = []
): React.ReactNode {
  const [mounted, setMounted] = React.useState(false);

  React.useEffect(() => {
    setMounted(true);
    return () => setMounted(false);
  }, deps);

  if (!mounted) {
    return null;
  }

  return useCppComponent(componentName, props);
}

// Hook for C++ component with ref
export function useCppComponentRef<T extends ReactProps>(
  componentName: string,
  props: T
): [React.ReactNode, React.MutableRefObject<HTMLElement | null>] {
  const ref = React.useRef<HTMLElement | null>(null);
  const component = useCppComponent(componentName, props);

  return [component, ref];
}

// Higher-order component for C++ components
export function withCppComponent<P extends object>(
  componentName: string,
  defaultProps?: Partial<P>
) {
  return function CppComponentWrapper(props: P) {
    const mergedProps = { ...defaultProps, ...props } as P;
    return useCppComponent(componentName, mergedProps);
  };
}

// Provider for C++ component context
export const CppComponentContext = React.createContext<{
  registerComponent: (name: string, component: React.ComponentType<ReactProps>) => void;
  getComponent: (name: string) => React.ComponentType<ReactProps> | undefined;
}>({
  registerComponent: () => {},
  getComponent: () => undefined,
});

export function CppComponentProvider({ children }: { children: React.ReactNode }) {
  const [components, setComponents] = React.useState<
    Map<string, React.ComponentType<any>>
  >(new Map());

  const registerComponent = React.useCallback(
    (name: string, component: React.ComponentType<ReactProps>) => {
      setComponents(prev => new Map(prev).set(name, component));
    },
    []
  );

  const getComponent = React.useCallback(
    (name: string) => components.get(name),
    [components]
  );

  return (
    <CppComponentContext.Provider value={{ registerComponent, getComponent }}>
      {children}
    </CppComponentContext.Provider>
  );
}

// Hook to use C++ component from context
export function useCppComponentFromContext(name: string) {
  const { getComponent } = React.useContext(CppComponentContext);
  return getComponent(name);
}
