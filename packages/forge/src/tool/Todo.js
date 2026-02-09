// FFI bindings for Tool.Todo PureScript module

// In-memory todo storage (in production, would use persistent storage)
const todoStorage = new Map();

// Store todos for a session
export const storeTodosFFI = (sessionId) => (todos) => () => {
  return new Promise((resolve) => {
    todoStorage.set(sessionId, todos);
    resolve(undefined);
  });
};

// Load todos for a session
export const loadTodosFFI = (sessionId) => () => {
  return new Promise((resolve) => {
    const todos = todoStorage.get(sessionId) || [];
    resolve(todos);
  });
};
