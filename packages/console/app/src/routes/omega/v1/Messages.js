// Messages Route FFI
// Only contains FFI implementations for PureScript foreign imports
// Route handler is implemented in Messages.purs

// Parse JSON field from request body (FFI boundary - JSON parsing)
export function parseJsonField(body, fieldName) {
  if (typeof body !== "string" || typeof fieldName !== "string") {
    return "";
  }
  
  try {
    const json = JSON.parse(body);
    if (json === null || typeof json !== "object") {
      return "";
    }
    
    const value = json[fieldName];
    if (value === null || value === undefined) {
      return "";
    }
    
    if (typeof value === "string") {
      return value;
    }
    
    if (typeof value === "boolean") {
      return value ? "true" : "false";
    }
    
    return String(value);
  } catch (e) {
    return "";
  }
}
