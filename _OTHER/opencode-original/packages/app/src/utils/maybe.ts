/**
 * Maybe/Option type implementation for protocol compliance
 * 
 * Replaces null/undefined usage with explicit Maybe pattern
 * following CODER type safety protocols.
 */

export type Maybe<T> = { type: 'just'; value: T } | { type: 'none' };

/**
 * Create a Maybe value containing a value
 */
export function just<T>(value: T): Maybe<T> {
  return { type: 'just', value };
}

/**
 * Create a Maybe value representing absence
 */
export function none<T>(): Maybe<T> {
  return { type: 'none' };
}

/**
 * Check if Maybe contains a value
 */
export function isJust<T>(maybe: Maybe<T>): maybe is { type: 'just'; value: T } {
  return maybe.type === 'just';
}

/**
 * Check if Maybe is empty
 */
export function isNone<T>(maybe: Maybe<T>): maybe is { type: 'none' } {
  return maybe.type === 'none';
}

/**
 * Extract value from Maybe, with fallback
 */
export function fromMaybe<T>(maybe: Maybe<T>, defaultValue: T): T {
  if (isJust(maybe)) {
    return maybe.value;
  }
  return defaultValue;
}

/**
 * Map over Maybe value
 */
export function mapMaybe<T, U>(maybe: Maybe<T>, fn: (value: T) => U): Maybe<U> {
  if (isJust(maybe)) {
    return just(fn(maybe.value));
  }
  return none();
}

/**
 * Chain Maybe operations
 */
export function bindMaybe<T, U>(maybe: Maybe<T>, fn: (value: T) => Maybe<U>): Maybe<U> {
  if (isJust(maybe)) {
    return fn(maybe.value);
  }
  return none();
}
