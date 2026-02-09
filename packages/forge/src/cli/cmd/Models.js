// FFI for Forge.CLI.Cmd.Models
// 1:1 parity with opencode-dev/packages/opencode/src/cli/cmd/models.ts

import { Provider } from "../../provider/Provider.js";
import { Log } from "../../util/Log.js";

const log = Log.create({ service: "cli.models" });

// Execute models command
export const executeFFI = (args) => async () => {
  try {
    if (args.list) {
      const result = await listModelsFFI(args.provider)();
      if (result.tag === "Left") {
        return result;
      }
      
      // Print models
      for (const model of result.value) {
        console.log(model);
      }
      
      return { tag: "Right", value: undefined };
    }
    
    if (args.info) {
      const parsed = Provider.parseModel(args.info);
      const model = await Provider.getModel(parsed.providerID, parsed.modelID);
      console.log(JSON.stringify(model, null, 2));
      return { tag: "Right", value: undefined };
    }
    
    // Default: list all models
    const result = await listModelsFFI(null)();
    if (result.tag === "Left") {
      return result;
    }
    
    for (const model of result.value) {
      console.log(model);
    }
    
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// List models
export const listModelsFFI = (providerID) => async () => {
  try {
    const providers = await Provider.list();
    const models = [];
    
    for (const [id, provider] of Object.entries(providers)) {
      if (providerID && id !== providerID) continue;
      
      for (const modelID of Object.keys(provider.models || {})) {
        models.push(`${id}/${modelID}`);
      }
    }
    
    return { tag: "Right", value: models.sort() };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
