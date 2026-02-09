// FFI for Forge.Tool.Tool
// 1:1 parity with opencode-dev/packages/opencode/src/tool/tool.ts

import { Log } from "../util/Log.js";

const log = Log.create({ service: "tool" });

// Tool definition function
export function define(id, init) {
  return {
    id,
    init: async (initCtx) => {
      const toolInfo = init instanceof Function ? await init(initCtx) : init;
      const execute = toolInfo.execute;
      
      toolInfo.execute = async (args, ctx) => {
        try {
          // Validate arguments if schema exists
          if (toolInfo.parameters?.parse) {
            toolInfo.parameters.parse(args);
          }
        } catch (error) {
          if (error.name === "ZodError" && toolInfo.formatValidationError) {
            throw new Error(toolInfo.formatValidationError(error), { cause: error });
          }
          throw new Error(
            `The ${id} tool was called with invalid arguments: ${error}.\nPlease rewrite the input so it satisfies the expected schema.`,
            { cause: error }
          );
        }
        
        const result = await execute(args, ctx);
        
        // Skip truncation for tools that handle it themselves
        if (result.metadata?.truncated !== undefined) {
          return result;
        }
        
        // Apply truncation if needed
        const { Truncate } = await import("./Truncation.js");
        const truncated = await Truncate.output(result.output, {}, initCtx?.agent);
        
        return {
          ...result,
          output: truncated.content,
          metadata: {
            ...result.metadata,
            truncated: truncated.truncated,
            ...(truncated.truncated && { outputPath: truncated.outputPath }),
          },
        };
      };
      
      return toolInfo;
    },
  };
}

// Tool namespace
export const Tool = {
  define,
};

// PureScript FFI exports
export const defineFFI = (id) => (init) => define(id, init);
