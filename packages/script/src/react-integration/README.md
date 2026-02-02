# React Integration - Phase 4

Complete React integration for the compiler pipeline.

## Components

### 1. React Hooks Generation

**Files**: `ReactHooksGenerator.h`, `ReactHooksGenerator.cpp`

Automatically generates React hooks from C++23 components:
- `useState` for state fields
- `useEffect` for effect functions
- `useRef` for ref fields
- `useCallback` for callback functions
- `useMemo` for memoized computations

**Usage**:
```cpp
// C++23 component with attributes
struct [[react_component]] MyComponent {
  [[state]] int count;
  [[effect]] void updateCount();
};
```

**Generated**:
```typescript
const [count, setCount] = useState<number>(0);
useEffect(() => {
  updateCount();
}, []);
```

### 2. State Management (Redux/Zustand)

**Files**: `StateManagement.h`, `StateManagement.cpp`

Generates state management stores:
- **Redux**: Redux Toolkit slices with actions and reducers
- **Zustand**: Zustand stores with actions

**Usage**:
```cpp
struct [[state_store]] AppState {
  int counter;
  std::string message;
};
```

**Generated Redux**:
```typescript
const counterSlice = createSlice({
  name: 'counter',
  initialState: { counter: 0, message: "" },
  reducers: {
    setCounter: (state, action) => { state.counter = action.payload; }
  }
});
```

**Generated Zustand**:
```typescript
export const useAppStateStore = create<AppState & AppStateActions>()(
  (set) => ({
    counter: 0,
    message: "",
    setCounter: (counter) => set({ counter })
  })
);
```

### 3. Context API Support

**Files**: `ContextAPI.h`, `ContextAPI.h`

Generates React Context providers and hooks:
- Context creation
- Provider components
- Custom hooks (`useContext` wrapper)
- Default values support

**Usage**:
```cpp
struct [[context]] ThemeContext {
  std::string theme;
  void toggleTheme();
};
```

**Generated**:
```typescript
const ThemeContext = createContext<ThemeContextValue | null>(null);

export const ThemeProvider: React.FC<ThemeProviderProps> = ({ children, theme }) => {
  const value: ThemeContextValue = { theme };
  return (
    <ThemeContext.Provider value={value}>
      {children}
    </ThemeContext.Provider>
  );
};

export const useTheme = (): ThemeContextValue => {
  const context = useContext(ThemeContext);
  if (!context) {
    throw new Error('useTheme must be used within ThemeProvider');
  }
  return context;
};
```

### 4. Suspense and Error Boundaries

**Files**: `SuspenseErrorBoundaries.h`, `SuspenseErrorBoundaries.cpp`

Generates:
- Error Boundary components (class components)
- Suspense wrappers
- Async component support

**Usage**:
```cpp
struct [[error_boundary]] MyComponent { };
struct [[suspense]] AsyncComponent { };
```

**Generated Error Boundary**:
```typescript
export class MyComponentErrorBoundary extends Component {
  static getDerivedStateFromError(error: Error) {
    return { hasError: true, error };
  }
  
  componentDidCatch(error: Error, errorInfo: ErrorInfo) {
    console.error('Error caught:', error, errorInfo);
  }
  
  render() {
    if (this.state.hasError) {
      return <div>Something went wrong</div>;
    }
    return this.props.children;
  }
}
```

**Generated Suspense**:
```typescript
export const AsyncComponentSuspense: React.FC = ({ children, fallback }) => {
  return (
    <Suspense fallback={fallback || <div>Loading...</div>}>
      {children}
    </Suspense>
  );
};
```

### 5. Server Components Support

**Files**: `ServerComponents.h`, `ServerComponents.cpp`

Generates React Server Components:
- Async server components
- Streaming server components
- Server-side data fetching

**Usage**:
```cpp
struct [[server_component]] ServerPage {
  [[server]] std::string fetchData();
};
```

**Generated**:
```typescript
export async function ServerPage(props: ServerPageProps) {
  const fetchDataResult = await fetchData();
  
  return (
    <div>
      {/* Server-rendered content */}
    </div>
  );
}
```

### 6. React Server Actions

**Files**: `ServerComponents.h`, `ServerComponents.cpp`

Generates server actions:
- Server action functions
- Form actions
- Revalidation support

**Usage**:
```cpp
[[server_action]] [[revalidate("/")]] void updateUser(int id);
[[form_action]] void submitForm(std::string data);
```

**Generated Server Action**:
```typescript
'use server';

export async function updateUser(id: number): Promise<void> {
  revalidatePath('/');
  // Implementation
}
```

**Generated Form Action**:
```typescript
'use server';

export async function submitFormAction(formData: FormData) {
  const data = formData.get('data') as string;
  await submitForm(data);
  revalidatePath('/');
  redirect('/success');
}
```

## Integration

All React integration features work together:
- Hooks integrate with state management
- Context API works with hooks
- Suspense wraps async components
- Error boundaries protect component trees
- Server components use server actions

## Status

✅ **All Phase 4 components implemented**

Ready for integration with the main compiler pipeline.
