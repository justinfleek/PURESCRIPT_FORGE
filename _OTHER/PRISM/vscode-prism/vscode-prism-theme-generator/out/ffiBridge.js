"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.generateThemeVariants = generateThemeVariants;
exports.generateThemeVariantsSync = generateThemeVariantsSync;
const child_process_1 = require("child_process");
/**
 * Generates theme variants by calling the Haskell FFI backend
 * @param config - Theme configuration with colors and settings
 * @returns Promise resolving to array of theme variants
 */
async function generateThemeVariants(config) {
    const input = JSON.stringify(config);
    return new Promise((resolve, reject) => {
        // Spawn the Haskell executable
        // Adjust path based on your setup - could be:
        // - "prism-theme-generator" (if in PATH)
        // - "./prism-theme-generator" (local binary)
        // - path.join(__dirname, "..", "bin", "prism-theme-generator")
        const proc = (0, child_process_1.spawn)("prism-theme-generator", ["generate"], {
            stdio: ["pipe", "pipe", "pipe"]
        });
        let stdout = "";
        let stderr = "";
        proc.stdout.on("data", (data) => {
            stdout += data.toString();
        });
        proc.stderr.on("data", (data) => {
            stderr += data.toString();
        });
        proc.on("close", (code) => {
            if (code !== 0) {
                reject(new Error(`FFI process exited with code ${code}: ${stderr}`));
                return;
            }
            try {
                const result = JSON.parse(stdout);
                resolve(result.variants);
            }
            catch (parseError) {
                reject(new Error(`Failed to parse FFI output: ${parseError}`));
            }
        });
        proc.on("error", (err) => {
            reject(new Error(`Failed to spawn FFI process: ${err.message}`));
        });
        // Write input to stdin and close
        proc.stdin.write(input);
        proc.stdin.end();
    });
}
/**
 * Alternative implementation using execSync for simpler cases
 * Note: This blocks the event loop - use sparingly
 */
function generateThemeVariantsSync(config) {
    const { execSync } = require("child_process");
    const input = JSON.stringify(config);
    try {
        const stdout = execSync("prism-theme-generator generate", {
            input,
            encoding: "utf8",
            maxBuffer: 10 * 1024 * 1024 // 10MB buffer for large outputs
        });
        const result = JSON.parse(stdout);
        return result.variants;
    }
    catch (error) {
        throw new Error(`FFI sync call failed: ${error}`);
    }
}
//# sourceMappingURL=ffiBridge.js.map