// FFI for Forge.Session.LLM
// 1:1 parity with opencode-dev/packages/opencode/src/session/llm.ts

import { Installation } from "../installation/Index.js";
import { Provider } from "../provider/Provider.js";
import { Log } from "../util/Log.js";
import {
  streamText,
  wrapLanguageModel,
  tool,
  jsonSchema,
} from "ai";
import { clone, mergeDeep, pipe } from "remeda";
import { ProviderTransform } from "../provider/Transform.js";
import { Config } from "../config/Config.js";
import { Instance } from "../project/Instance.js";
import { Plugin } from "../plugin/Index.js";
import { SystemPrompt } from "./System.js";
import { Flag } from "../flag/Flag.js";
import { PermissionNext } from "../permission/Next.js";
import { Auth } from "../auth/Index.js";

const log = Log.create({ service: "llm" });

export const outputTokenMax = Flag.FORGE_EXPERIMENTAL_OUTPUT_TOKEN_MAX || 32000;

export const stream = (input) => async () => {
  const l = log
    .clone()
    .tag("providerID", input.model.providerID)
    .tag("modelID", input.model.id)
    .tag("sessionID", input.sessionID)
    .tag("small", (input.small ?? false).toString())
    .tag("agent", input.agent.name)
    .tag("mode", input.agent.mode);
  l.info("stream", {
    modelID: input.model.id,
    providerID: input.model.providerID,
  });
  
  const [language, cfg, provider, auth] = await Promise.all([
    Provider.getLanguage(input.model),
    Config.get(),
    Provider.getProvider(input.model.providerID),
    Auth.get(input.model.providerID),
  ]);
  const isCodex = provider.id === "openai" && auth?.type === "oauth";

  const system = [];
  system.push(
    [
      ...(input.agent.prompt ? [input.agent.prompt] : isCodex ? [] : SystemPrompt.provider(input.model)),
      ...input.system,
      ...(input.user.system ? [input.user.system] : []),
    ]
      .filter((x) => x)
      .join("\n"),
  );

  const header = system[0];
  const original = clone(system);
  await Plugin.trigger(
    "experimental.chat.system.transform",
    { sessionID: input.sessionID, model: input.model },
    { system },
  );
  if (system.length === 0) {
    system.push(...original);
  }
  if (system.length > 2 && system[0] === header) {
    const rest = system.slice(1);
    system.length = 0;
    system.push(header, rest.join("\n"));
  }

  const variant =
    !input.small && input.model.variants && input.user.variant ? input.model.variants[input.user.variant] : {};
  const base = input.small
    ? ProviderTransform.smallOptions(input.model)
    : ProviderTransform.options({
        model: input.model,
        sessionID: input.sessionID,
        providerOptions: provider.options,
      });
  const options = pipe(
    base,
    mergeDeep(input.model.options),
    mergeDeep(input.agent.options),
    mergeDeep(variant),
  );
  if (isCodex) {
    options.instructions = SystemPrompt.instructions();
  }

  const params = await Plugin.trigger(
    "chat.params",
    {
      sessionID: input.sessionID,
      agent: input.agent,
      model: input.model,
      provider,
      message: input.user,
    },
    {
      temperature: input.model.capabilities.temperature
        ? (input.agent.temperature ?? ProviderTransform.temperature(input.model))
        : undefined,
      topP: input.agent.topP ?? ProviderTransform.topP(input.model),
      topK: ProviderTransform.topK(input.model),
      options,
    },
  );

  const { headers } = await Plugin.trigger(
    "chat.headers",
    {
      sessionID: input.sessionID,
      agent: input.agent,
      model: input.model,
      provider,
      message: input.user,
    },
    {
      headers: {},
    },
  );

  const maxOutputTokens = isCodex
    ? undefined
    : ProviderTransform.maxOutputTokens(
        input.model.api.npm,
        params.options,
        input.model.limit.output,
        outputTokenMax,
      );

  const tools = await resolveTools(input);

  const isLiteLLMProxy =
    provider.options?.["litellmProxy"] === true ||
    input.model.providerID.toLowerCase().includes("litellm") ||
    input.model.api.id.toLowerCase().includes("litellm");

  if (isLiteLLMProxy && Object.keys(tools).length === 0 && hasToolCalls(input.messages)) {
    tools["_noop"] = tool({
      description:
        "Placeholder for LiteLLM/Anthropic proxy compatibility - required when message history contains tool calls but no active tools are needed",
      inputSchema: jsonSchema({ type: "object", properties: {} }),
      execute: async () => ({ output: "", title: "", metadata: {} }),
    });
  }

  return streamText({
    onError(error) {
      l.error("stream error", {
        error,
      });
    },
    async experimental_repairToolCall(failed) {
      const lower = failed.toolCall.toolName.toLowerCase();
      if (lower !== failed.toolCall.toolName && tools[lower]) {
        l.info("repairing tool call", {
          tool: failed.toolCall.toolName,
          repaired: lower,
        });
        return {
          ...failed.toolCall,
          toolName: lower,
        };
      }
      return {
        ...failed.toolCall,
        input: JSON.stringify({
          tool: failed.toolCall.toolName,
          error: failed.error.message,
        }),
        toolName: "invalid",
      };
    },
    temperature: params.temperature,
    topP: params.topP,
    topK: params.topK,
    providerOptions: ProviderTransform.providerOptions(input.model, params.options),
    activeTools: Object.keys(tools).filter((x) => x !== "invalid"),
    tools,
    maxOutputTokens,
    abortSignal: input.abort,
    headers: {
      ...(input.model.providerID.startsWith("forge")
        ? {
            "x-forge-project": Instance.project.id,
            "x-forge-session": input.sessionID,
            "x-forge-request": input.user.id,
            "x-forge-client": Flag.FORGE_CLIENT,
          }
        : input.model.providerID !== "anthropic"
          ? {
              "User-Agent": `forge/${Installation.VERSION}`,
            }
          : undefined),
      ...input.model.headers,
      ...headers,
    },
    maxRetries: input.retries ?? 0,
    messages: [
      ...(isCodex
        ? [
            {
              role: "user",
              content: system.join("\n\n"),
            },
          ]
        : system.map((x) => ({
            role: "system",
            content: x,
          }))),
      ...input.messages,
    ],
    model: wrapLanguageModel({
      model: language,
      middleware: [
        {
          async transformParams(args) {
            if (args.type === "stream") {
              args.params.prompt = ProviderTransform.message(args.params.prompt, input.model, options);
            }
            return args.params;
          },
        },
      ],
    }),
    experimental_telemetry: {
      isEnabled: cfg.experimental?.openTelemetry,
      metadata: {
        userId: cfg.username ?? "unknown",
        sessionId: input.sessionID,
      },
    },
  });
};

async function resolveTools(input) {
  const disabled = PermissionNext.disabled(Object.keys(input.tools), input.agent.permission);
  for (const tool of Object.keys(input.tools)) {
    if (input.user.tools?.[tool] === false || disabled.has(tool)) {
      delete input.tools[tool];
    }
  }
  return input.tools;
}

export const hasToolCalls = (messages) => {
  for (const msg of messages) {
    if (!Array.isArray(msg.content)) continue;
    for (const part of msg.content) {
      if (part.type === "tool-call" || part.type === "tool-result") return true;
    }
  }
  return false;
};
