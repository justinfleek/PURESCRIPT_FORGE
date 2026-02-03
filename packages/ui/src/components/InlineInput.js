// InlineInput FFI - Keyboard event key extraction

/**
 * Extract key from keyboard event
 * @param {KeyboardEvent} event
 * @returns {string}
 */
export const keyFromEvent = (event) => event.key || '';
