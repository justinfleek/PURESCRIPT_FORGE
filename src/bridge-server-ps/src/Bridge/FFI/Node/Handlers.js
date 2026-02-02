// JSON-RPC Request/Response Decoding/Encoding - ES Module

// Helper: Explicit default value
const explicitDefault = (value, defaultValue) => {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
};

// Helper: Create Right
const right = (value) => ({ tag: "Right", value });

// Helper: Create Left
const left = (value) => ({ tag: "Left", value });

// Helper: Wrap in Just
const just = (value) => ({ tag: "Just", value });

// Helper: Nothing
const nothing = { tag: "Nothing" };

// Helper: toMaybe
const toMaybe = (value) => (value === null || value === undefined) ? nothing : just(value);

// | Decode session.new request
export const decodeSessionNewRequest = (json) => () => {
  try {
    const obj = JSON.parse(json);
    return right({
      name: toMaybe(obj.name),
      parentId: toMaybe(obj.parentId),
      model: toMaybe(obj.model),
      provider: toMaybe(obj.provider)
    });
  } catch (e) {
    return left("Invalid JSON: " + e.message);
  }
};

// | Decode file.context.add request
export const decodeFileContextAddRequest = (json) => () => {
  try {
    const obj = JSON.parse(json);
    return right({
      path: explicitDefault(obj.path, ""),
      sessionId: toMaybe(obj.sessionId)
    });
  } catch (e) {
    return left("Invalid JSON: " + e.message);
  }
};

// | Decode file.context.list request
export const decodeFileContextListRequest = (maybParams) => () => {
  if (!maybParams || maybParams.tag === "Nothing") {
    return right({
      sessionId: nothing,
      filter: nothing
    });
  }
  try {
    const params = maybParams.tag === "Just" ? maybParams.value : maybParams;
    const obj = typeof params === "string" ? JSON.parse(params) : params;
    return right({
      sessionId: toMaybe(obj.sessionId),
      filter: toMaybe(obj.filter)
    });
  } catch (e) {
    return left("Invalid JSON: " + e.message);
  }
};

// | Decode terminal.execute request
export const decodeTerminalExecuteRequest = (json) => () => {
  try {
    const obj = JSON.parse(json);
    return right({
      command: explicitDefault(obj.command, ""),
      cwd: toMaybe(obj.cwd),
      sessionId: toMaybe(obj.sessionId)
    });
  } catch (e) {
    return left("Invalid JSON: " + e.message);
  }
};

// | Encode session.new response
export const encodeSessionNewResponse = (response) => () => {
  return JSON.stringify({
    sessionId: response.sessionId,
    success: response.success
  });
};

// | Encode file.context.add response
export const encodeFileContextAddResponse = (response) => () => {
  return JSON.stringify(response);
};

// | Encode file.context.list response
export const encodeFileContextListResponse = (response) => () => {
  return JSON.stringify(response);
};

// | Encode terminal.execute response
export const encodeTerminalExecuteResponse = (response) => () => {
  return JSON.stringify(response);
};

// | Decode web.search request
export const decodeWebSearchRequest = (json) => () => {
  try {
    const obj = JSON.parse(json);
    return right({
      query: explicitDefault(obj.query, ""),
      maxResults: toMaybe(obj.maxResults),
      sessionId: toMaybe(obj.sessionId)
    });
  } catch (e) {
    return left("Invalid JSON: " + e.message);
  }
};

// | Encode web.search response
export const encodeWebSearchResponse = (response) => () => {
  return JSON.stringify(response);
};

// | Decode alerts.configure request
export const decodeAlertsConfigureRequest = (json) => () => {
  try {
    const obj = JSON.parse(json);
    return right({
      diemWarningPercent: explicitDefault(obj.diemWarningPercent, 20),
      diemCriticalPercent: explicitDefault(obj.diemCriticalPercent, 5),
      depletionWarningHours: explicitDefault(obj.depletionWarningHours, 2)
    });
  } catch (e) {
    return left("Invalid JSON: " + e.message);
  }
};

// | Generate authentication token
export const generateAuthToken = () => {
  // Generate a random token
  const chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';
  let token = '';
  for (let i = 0; i < 32; i++) {
    token += chars.charAt(Math.floor(Math.random() * chars.length));
  }
  return token;
};

// | Get authentication token expiry
export const getAuthTokenExpiry = () => {
  // Return expiry as ISO string (24 hours from now)
  const expiry = new Date(Date.now() + 24 * 60 * 60 * 1000);
  return expiry.toISOString();
};

// | Decode auth.validate request
export const decodeAuthValidateRequest = (json) => () => {
  try {
    const obj = JSON.parse(json);
    return right({
      token: explicitDefault(obj.token, "")
    });
  } catch (e) {
    return left("Invalid JSON: " + e.message);
  }
};

// | Validate authentication token
export const validateAuthToken = (token) => () => {
  // For now, just check that token is non-empty
  return token && token.length > 0;
};

// | Decode settings.save request
export const decodeSettingsSaveRequest = (json) => () => {
  try {
    const obj = JSON.parse(json);
    return right({
      alerts: {
        warningPercent: explicitDefault(obj.alerts?.warningPercent, 20),
        criticalPercent: explicitDefault(obj.alerts?.criticalPercent, 5),
        warningHours: explicitDefault(obj.alerts?.warningHours, 2),
        soundEnabled: explicitDefault(obj.alerts?.soundEnabled, true)
      },
      appearance: {
        theme: explicitDefault(obj.appearance?.theme, "system")
      },
      keyboard: {
        enabled: explicitDefault(obj.keyboard?.enabled, true),
        vimMode: explicitDefault(obj.keyboard?.vimMode, false)
      },
      features: {
        countdown: explicitDefault(obj.features?.countdown, true),
        tokenCharts: explicitDefault(obj.features?.tokenCharts, true),
        proofPanel: explicitDefault(obj.features?.proofPanel, true),
        timeline: explicitDefault(obj.features?.timeline, true)
      },
      storage: {
        retentionDays: explicitDefault(obj.storage?.retentionDays, 30)
      }
    });
  } catch (e) {
    return left("Invalid JSON: " + e.message);
  }
};

// | Encode settings.save response
export const encodeSettingsSaveResponse = (response) => () => {
  return JSON.stringify({ success: response.success });
};

// | Decode file.read request
export const decodeFileReadRequest = (json) => () => {
  try {
    const obj = JSON.parse(json);
    return right({
      path: explicitDefault(obj.path, "")
    });
  } catch (e) {
    return left("Invalid JSON: " + e.message);
  }
};

// | Encode file.read response
export const encodeFileReadResponse = (response) => () => {
  return JSON.stringify({
    success: response.success,
    content: response.content?.tag === "Just" ? response.content.value : null,
    error: response.error?.tag === "Just" ? response.error.value : null
  });
};

// | Decode lean.applyTactic request
export const decodeLeanApplyTacticRequest = (json) => () => {
  try {
    const obj = JSON.parse(json);
    return right({
      file: explicitDefault(obj.file, ""),
      line: explicitDefault(obj.line, 0),
      column: explicitDefault(obj.column, 0),
      tactic: explicitDefault(obj.tactic, ""),
      goalIndex: toMaybe(obj.goalIndex)
    });
  } catch (e) {
    return left("Invalid JSON: " + e.message);
  }
};

// | Encode lean.applyTactic response
export const encodeLeanApplyTacticResponse = (response) => () => {
  return JSON.stringify({
    success: response.success,
    message: response.message?.tag === "Just" ? response.message.value : null,
    goals: response.goals.map(g => ({
      type: g.type_,
      context: g.context.map(c => ({ name: c.name, type: c.type_ }))
    }))
  });
};

// | Decode lean.searchTheorems request
export const decodeLeanSearchTheoremsRequest = (json) => () => {
  try {
    const obj = JSON.parse(json);
    return right({
      query: explicitDefault(obj.query, ""),
      limit: toMaybe(obj.limit),
      file: toMaybe(obj.file)
    });
  } catch (e) {
    return left("Invalid JSON: " + e.message);
  }
};

// | Encode lean.searchTheorems response
export const encodeLeanSearchTheoremsResponse = (response) => () => {
  return JSON.stringify({
    theorems: response.theorems.map(t => ({
      name: t.name,
      statement: t.statement,
      file: t.file,
      line: t.line,
      description: t.description?.tag === "Just" ? t.description.value : null
    })),
    total: response.total
  });
};
