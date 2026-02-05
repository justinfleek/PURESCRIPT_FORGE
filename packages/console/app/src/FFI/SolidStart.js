// SolidJS Start FFI
// Wraps SolidJS Start server API functions

import { redirect as solidRedirect } from "@solidjs/router";
import { APIEvent } from "@solidjs/start/server";

// Opaque types are just passed through
export const redirect = (url) => {
  return Promise.resolve(solidRedirect(url));
};

export const jsonResponse = (jsonString) => {
  return Promise.resolve(Response.json(JSON.parse(jsonString)));
};

export const textResponse = (text, status) => {
  return Promise.resolve(new Response(text, { status }));
};

export const getRequest = (event) => {
  return event.request;
};

export const getRequestUrl = (request) => {
  return new URL(request.url);
};

export const getSearchParams = (url) => {
  return url.searchParams;
};

export const getHeader = (request, name) => {
  const value = request.headers.get(name);
  return value === null ? undefined : value;
};

export const setLocals = (event, key, value) => {
  if (event.locals) {
    event.locals[key] = value;
  }
};

export const getLocals = (event, key) => {
  if (event.locals) {
    const value = event.locals[key];
    return value === undefined ? undefined : value;
  }
  return undefined;
};

export const getSearchParam = (searchParams, name) => {
  const value = searchParams.get(name);
  return value === null ? undefined : value;
};

export const createURL = (urlString) => {
  return new URL(urlString);
};
