// FFI for UseFilteredList Hook

import fuzzysort from "fuzzysort";

// Perform fuzzy search on items
export const fuzzySearch = (items) => (needle) => (mFilterKeys) => () => {
  const query = needle.toLowerCase();
  
  if (!query) {
    return items;
  }
  
  // If filterKeys is provided, use object search
  if (mFilterKeys && mFilterKeys.length > 0) {
    return fuzzysort.go(query, items, { keys: mFilterKeys }).map((x) => x.obj);
  }
  
  // If items are strings, search directly
  if (items.length > 0 && typeof items[0] === "string") {
    return fuzzysort.go(query, items).map((x) => x.target);
  }
  
  // Default: return filtered based on stringified representation
  return items.filter((item) => 
    JSON.stringify(item).toLowerCase().includes(query)
  );
};

// Get key from keyboard event
export const getEventKey = (event) => () => {
  return event.key;
};
