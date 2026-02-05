// OpenAPI JSON Route FFI
// Wraps SolidJS Start route handler

export const handleOpenApiGET = async (event) => {
  const response = await fetch(
    "https://raw.githubusercontent.com/anomalyco/opencode/refs/heads/dev/packages/sdk/openapi.json"
  );
  const json = await response.json();
  return Response.json(json);
};

export const fetchJson = async (url) => {
  const response = await fetch(url);
  return await response.json();
};

export const toJsonString = (json) => {
  return JSON.stringify(json);
};
