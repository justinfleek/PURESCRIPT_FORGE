// Session Proxy Route FFI
// Proxies requests to docs.opencode.ai/docs/{sessionId}...
//
// Source: _OTHER/opencode-original/packages/console/app/src/routes/s/[id].ts
// Migrated: 2026-02-04

export async function handleSessionProxy(event, sessionId) {
  const req = event.request.clone();
  const url = new URL(req.url);
  const targetUrl = `https://docs.opencode.ai/docs/${sessionId}${url.pathname}${url.search}`;
  
  const response = await fetch(targetUrl, {
    method: req.method,
    headers: req.headers,
    body: req.body,
  });
  
  return response;
}
