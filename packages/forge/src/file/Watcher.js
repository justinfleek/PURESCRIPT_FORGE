// Forge.File.Watcher FFI - File system watching
// Uses chokidar for cross-platform file watching

import * as fs from 'fs';

// Simple file watcher using fs.watch (built-in, no dependencies)
// For production, consider using chokidar for better cross-platform support
export const watchDirectoryFFI = (watchPath) => (options) => (handler) => async () => {
  try {
    const watchers = [];
    
    // Map to track debouncing
    const debounceMap = new Map();
    
    const handleEvent = (eventType, filename) => {
      if (!filename) return;
      
      const fullPath = watchPath + '/' + filename;
      
      // Check if should be ignored
      for (const pattern of options.ignored) {
        if (fullPath.includes(pattern) || filename.includes(pattern)) {
          return;
        }
      }
      
      // Debounce
      const key = eventType + ':' + fullPath;
      if (debounceMap.has(key)) {
        clearTimeout(debounceMap.get(key));
      }
      
      debounceMap.set(key, setTimeout(() => {
        debounceMap.delete(key);
        
        // Determine event type
        let eventName;
        if (eventType === 'rename') {
          // Check if file exists to determine if it was created or deleted
          try {
            fs.accessSync(fullPath);
            eventName = 'add';
          } catch {
            eventName = 'unlink';
          }
        } else {
          eventName = 'change';
        }
        
        // Call handler: eventType -> path -> Maybe oldPath -> Effect Unit
        handler(eventName)(fullPath)(null)();
      }, options.debounceMs));
    };
    
    // Watch the directory
    const watcher = fs.watch(watchPath, { recursive: options.recursive }, handleEvent);
    watchers.push(watcher);
    
    // Return close function
    return {
      tag: 'Right',
      value: {
        close: () => {
          for (const w of watchers) {
            w.close();
          }
          debounceMap.clear();
        }
      }
    };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
