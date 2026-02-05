// Changelog JSON Route FFI
// Wraps SolidJS Start route handler

import { loadChangelog } from "../lib/Changelog.js";

const cors = {
  "Access-Control-Allow-Origin": "*",
  "Access-Control-Allow-Methods": "GET, OPTIONS",
  "Access-Control-Allow-Headers": "Content-Type, Authorization",
};

const ok = "public, max-age=1, s-maxage=300, stale-while-revalidate=86400, stale-if-error=86400";
const error = "public, max-age=1, s-maxage=60, stale-while-revalidate=600, stale-if-error=86400";

export const handleChangelogGET = async (event) => {
  try {
    const result = await loadChangelog();
    return new Response(JSON.stringify({ releases: result.releases }), {
      status: result.ok ? 200 : 503,
      headers: {
        "Content-Type": "application/json",
        "Cache-Control": result.ok ? ok : error,
        ...cors,
      },
    });
  } catch (error) {
    return new Response(JSON.stringify({ releases: [] }), {
      status: 503,
      headers: {
        "Content-Type": "application/json",
        "Cache-Control": error,
        ...cors,
      },
    });
  }
};

export const handleChangelogOPTIONS = async (event) => {
  return new Response(null, {
    status: 200,
    headers: cors,
  });
};

export const toJsonString = (data) => {
  return JSON.stringify(data);
};
