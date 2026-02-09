// FFI for Forge.Provider.Auth
// 1:1 parity with opencode-dev/packages/opencode/src/provider/auth.ts

import { Instance } from "../project/Instance.js";
import { Plugin } from "../plugin/Index.js";
import { map, filter, pipe, fromEntries, mapValues } from "remeda";
import { fn } from "../util/Fn.js";
import { NamedError } from "../util/Error.js";
import { Auth } from "../auth/Index.js";

const state = Instance.state(async () => {
  const methods = pipe(
    await Plugin.list(),
    filter((x) => x.auth?.provider !== undefined),
    map((x) => [x.auth.provider, x.auth]),
    fromEntries(),
  );
  return { methods, pending: {} };
});

export const methods = async () => {
  const s = await state().then((x) => x.methods);
  return mapValues(s, (x) =>
    x.methods.map((y) => ({
      type: y.type,
      label: y.label,
    })),
  );
};

export const authorize = (input) => async () => {
  const auth = await state().then((s) => s.methods[input.providerID]);
  const method = auth.methods[input.method];
  if (method.type === "oauth") {
    const result = await method.authorize();
    await state().then((s) => (s.pending[input.providerID] = result));
    return {
      url: result.url,
      method: result.method,
      instructions: result.instructions,
    };
  }
  return null;
};

export const callback = (input) => async () => {
  const match = await state().then((s) => s.pending[input.providerID]);
  if (!match) throw new OauthMissing({ providerID: input.providerID });
  let result;

  if (match.method === "code") {
    if (!input.code) throw new OauthCodeMissing({ providerID: input.providerID });
    result = await match.callback(input.code);
  }

  if (match.method === "auto") {
    result = await match.callback();
  }

  if (result?.type === "success") {
    if ("key" in result) {
      await Auth.set(input.providerID, {
        type: "api",
        key: result.key,
      });
    }
    if ("refresh" in result) {
      const info = {
        type: "oauth",
        access: result.access,
        refresh: result.refresh,
        expires: result.expires,
      };
      if (result.accountId) {
        info.accountId = result.accountId;
      }
      await Auth.set(input.providerID, info);
    }
    return;
  }

  throw new OauthCallbackFailed({});
};

export const api = (input) => async () => {
  await Auth.set(input.providerID, {
    type: "api",
    key: input.key,
  });
};

export const OauthMissing = NamedError.create(
  "ProviderAuthOauthMissing",
  { providerID: "string" },
);

export const OauthCodeMissing = NamedError.create(
  "ProviderAuthOauthCodeMissing",
  { providerID: "string" },
);

export const OauthCallbackFailed = NamedError.create(
  "ProviderAuthOauthCallbackFailed",
  {},
);
