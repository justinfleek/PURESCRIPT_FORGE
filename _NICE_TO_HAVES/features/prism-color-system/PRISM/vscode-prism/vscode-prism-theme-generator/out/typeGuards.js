"use strict";
// Type guards for deterministic type narrowing (no assertions)
Object.defineProperty(exports, "__esModule", { value: true });
exports.isHTMLInputElement = isHTMLInputElement;
exports.isHTMLElement = isHTMLElement;
exports.isValidMonitorType = isValidMonitorType;
exports.isValidThemeMode = isValidThemeMode;
exports.getVSCodeAPI = getVSCodeAPI;
exports.getColorOrDefault = getColorOrDefault;
function isHTMLInputElement(value) {
    if (value === null) {
        return false;
    }
    return value instanceof HTMLInputElement;
}
function isHTMLElement(value) {
    if (value === null) {
        return false;
    }
    return value instanceof HTMLElement;
}
function isValidMonitorType(value) {
    return value === "OLED" || value === "LCD";
}
function isValidThemeMode(value) {
    return value === "dark" || value === "light";
}
function getVSCodeAPI() {
    // Check if acquireVsCodeApi exists on window
    const windowObj = window;
    if (typeof windowObj.acquireVsCodeApi === "function") {
        return windowObj.acquireVsCodeApi();
    }
    throw new Error("VSCode API not available - acquireVsCodeApi not found");
}
// Safe color access with explicit defaults
function getColorOrDefault(colors, key, defaultValue) {
    const value = colors[key];
    if (value === undefined || value === null || value === "") {
        return defaultValue;
    }
    return value;
}
//# sourceMappingURL=typeGuards.js.map