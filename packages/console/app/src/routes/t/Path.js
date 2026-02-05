// Enterprise Proxy Route FFI
// Proxies requests to enterprise.opencode.ai

export async function proxyRequest(event) {
  const req = event.request.clone();
  const url = new URL(req.url);
  const targetUrl = `https://enterprise.opencode.ai/${url.pathname}${url.search}`;
  const response = await fetch(targetUrl, {
    method: req.method,
    headers: req.headers,
    body: req.body,
  });
  return response;
}
