// Entry Server FFI
// Wraps SolidJS Start server handler creation

import { createHandler, StartServer } from "@solidjs/start/server";

const criticalCSS = `[data-component="top"]{min-height:80px;display:flex;align-items:center}`;

export const createServerHandler = () => {
  return createHandler(
    () => (
      <StartServer
        document={({ assets, children, scripts }) => (
          <html lang="en">
            <head>
              <meta charSet="utf-8" />
              <meta name="viewport" content="width=device-width, initial-scale=1" />
              <meta property="og:image" content="/social-share.png" />
              <meta property="twitter:image" content="/social-share.png" />
              <style>{criticalCSS}</style>
              {assets}
            </head>
            <body>
              <div id="app">{children}</div>
              {scripts}
            </body>
          </html>
        )}
      />
    ),
    {
      mode: "async",
    }
  );
};
