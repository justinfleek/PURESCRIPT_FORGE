// Express.js FFI - ES Module

// Stub express implementation for compilation
const createExpressApp = () => {
  const routes = { get: {} };
  const middlewares = [];
  
  return {
    get: (route, handler) => { routes.get[route] = handler; },
    use: (middleware) => { middlewares.push(middleware); },
    _routes: routes,
    _middlewares: middlewares
  };
};

export const createApp = () => () => {
  return createExpressApp();
};

export const createServer = (app) => () => {
  // Stub HTTP server
  return {
    _app: app,
    listen: (port, host, cb) => {
      console.log(`Server listening on ${host}:${port}`);
      if (cb) cb();
    }
  };
};

export const listen = (server) => (port) => (host) => (callback) => () => {
  if (server && server.listen) {
    server.listen(port, host, () => {
      callback();
    });
  }
};

export const get = (app) => (route) => (handler) => () => {
  if (app && app.get) {
    app.get(route, (req, res) => {
      handler(req)(res)();
    });
  }
};

export const useStatic = (app) => (dir) => () => {
  if (app && app.use) {
    // Stub static middleware
    app.use({ type: 'static', dir });
  }
};

export const sendJson = (res) => (json) => () => {
  if (res && res.json) {
    res.json(JSON.parse(json));
  } else {
    console.log('JSON response:', json);
  }
};

export const sendFile = (res) => (root) => (file) => () => {
  if (res && res.sendFile) {
    res.sendFile(file, { root });
  } else {
    console.log('File response:', root, file);
  }
};

export const getPath = (req) => () => {
  return req && req.path ? req.path : '/';
};

export const getMethod = (req) => () => {
  return req && req.method ? req.method : 'GET';
};
