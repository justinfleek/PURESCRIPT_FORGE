import { spawn } from "child_process";
import { ThemeConfig, ThemeVariant } from "./types";

/**
 * FFI Bridge to Haskell theme generation backend
 * Uses spawn instead of exec to support stdin input
 */

interface FFIResult {
  variants: ThemeVariant[];
}

/**
 * Generates theme variants by calling the Haskell FFI backend
 * @param config - Theme configuration with colors and settings
 * @returns Promise resolving to array of theme variants
 */
export async function generateThemeVariants(config: ThemeConfig): Promise<ThemeVariant[]> {
  const input = JSON.stringify(config);
  
  return new Promise((resolve, reject) => {
    // Spawn the Haskell executable
    // Adjust path based on your setup - could be:
    // - "prism-theme-generator" (if in PATH)
    // - "./prism-theme-generator" (local binary)
    // - path.join(__dirname, "..", "bin", "prism-theme-generator")
    const proc = spawn("prism-theme-generator", ["generate"], {
      stdio: ["pipe", "pipe", "pipe"]
    });

    let stdout = "";
    let stderr = "";

    proc.stdout.on("data", (data: Buffer) => {
      stdout += data.toString();
    });

    proc.stderr.on("data", (data: Buffer) => {
      stderr += data.toString();
    });

    proc.on("close", (code: number | null) => {
      if (code !== 0) {
        reject(new Error(`FFI process exited with code ${code}: ${stderr}`));
        return;
      }

      try {
        const result: FFIResult = JSON.parse(stdout);
        resolve(result.variants);
      } catch (parseError) {
        reject(new Error(`Failed to parse FFI output: ${parseError}`));
      }
    });

    proc.on("error", (err: Error) => {
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
export function generateThemeVariantsSync(config: ThemeConfig): ThemeVariant[] {
  const { execSync } = require("child_process");
  const input = JSON.stringify(config);
  
  try {
    const stdout = execSync("prism-theme-generator generate", {
      input,
      encoding: "utf8",
      maxBuffer: 10 * 1024 * 1024 // 10MB buffer for large outputs
    });
    
    const result: FFIResult = JSON.parse(stdout);
    return result.variants;
  } catch (error) {
    throw new Error(`FFI sync call failed: ${error}`);
  }
}
